#include <iostream>
#include <string>
#include <vector>
#include <set>
#include <map>
#include <unordered_set>
#include <unordered_map>
#include <algorithm>

typedef int Cost;
typedef std::vector<bool> State;
static const Cost INF = 0x3f3f3f3f;

inline bool contains(const State& s1, const State& s2)
{
	for (int i = 0; i < s1.size(); ++i)
		if (!s1[i] && s2[i])
			return false;
	return true;
}

struct Operator
{
	Cost cost;
	std::string name;
	State preconditions;
	State add_effects;
	State del_effects;
	std::vector<Operator> suboperators;
	void apply(State& s) const
	{
		if (!contains(s, preconditions))
			return;
		for (int i = 0; i < s.size(); ++i)
			s[i] = (s[i] && !del_effects[i]) || add_effects[i];
		for (const Operator& subop : suboperators)
			subop.apply(s);
	}
	void apply_relaxed(State& s) const
	{
		if (!contains(s, preconditions))
			return;
		for (int i = 0; i < s.size(); ++i)
			s[i] = s[i] || add_effects[i];
		for (const Operator& subop : suboperators)
			subop.apply_relaxed(s);
	}
	void inv_apply_relaxed(State& s) const
	{
		for (int i = 0; i < s.size(); ++i)
			s[i] = (s[i] && !add_effects[i]) || preconditions[i];
		for (const Operator& subop : suboperators)
			subop.inv_apply_relaxed(s); // TODO: this line is wrong
	}
};

struct Heuristic
{
	virtual Cost estimate(std::vector<Operator>& ops, const State& start, const State& goal)
	{
		return 0;
	}
};

struct HSP : Heuristic
{
	std::vector<Cost> g;
	Cost sum(const State& s)
	{
		Cost ret = 0;
		for (int i = 0; i < g.size(); ++i)
			if (s[i])
				ret += g[i];
		return ret;
	}
	virtual Cost estimate(std::vector<Operator>& ops, const State& start, const State& goal)
	{
		g.clear();
		for (const bool& v : start)
		{
			if (v)
				g.push_back(0);
			else
				g.push_back(INF);
		}
		bool change = true;
		while (change)
		{
			change = false;
			for (const Operator& op : ops)
			{
				Cost cost_estimate = sum(op.preconditions) + op.cost;
				for (int i = 0; i < g.size(); ++i)
				if (op.add_effects[i] && g[i] > cost_estimate)
				{
					g[i] = cost_estimate;
					change = true;
				}
			}
		}
		return sum(goal);
	}
};

struct FF : Heuristic
{
	std::vector<Cost> g;
	virtual Cost estimate(std::vector<Operator>& ops, const State& start, const State& goal)
	{
		g.clear();
		for (const bool& v : start)
		{
			if (v)
				g.push_back(0);
			else
				g.push_back(INF);
		}
		std::vector<State> state_layers;
		std::vector<std::vector<Operator*> > op_layers;
		state_layers.push_back(start);
		while (!contains(state_layers.back(), goal))
		{
			State next_state = state_layers.back();
			op_layers.push_back(std::vector<Operator*>());
			for (Operator& op : ops)
				if (contains(state_layers.back(), op.preconditions))
				{
					op_layers.back().push_back(&op);
					op.apply_relaxed(next_state);
				}
			if (state_layers.back() == next_state)
				return INF;
			for (int i = 0; i < g.size(); ++i)
				if (!state_layers.back()[i] && next_state[i])
					g[i] = state_layers.size();
			state_layers.push_back(next_state);
		}
		Cost cost = 0;
		State subgoal = goal;
		for (int i = op_layers.size(); i > 0; --i)
		{
			;
			// NOTES
			// Among operators with g[op] = i and add effect in subgoal, min sum(g[prec])
			// pass operator schemata and instantiate only reachable ops
			// when new atom is added, increment #precs of ops and subops
		}
		return cost;
	}
};

struct StateData
{
	Cost g, h;
	State prev_state;
	Operator* prev_op;
	std::multimap<Cost, State>::iterator iter;
};

struct Problem
{
	std::vector<std::string> atom_names;
	std::vector<Operator> operators;
	std::unordered_map<State, StateData> data;
	State AStar(Heuristic& heur, const State& start, const State& goal)
	{
		std::multimap<Cost, State> frontier;
		StateData& s_data = data[start];
		s_data.g = 0;
		s_data.h = heur.estimate(operators, start, goal);
		frontier.clear();
		frontier.insert(std::pair<Cost, State>(s_data.h, start));
		while (!frontier.empty())
		{
			State s = frontier.begin()->second;
			if (contains(s, goal))
				return s;
			frontier.erase(frontier.begin());
			s_data = data[s];
			for (Operator op : operators)
			{
				State t = s;
				op.apply(t);
				StateData& t_data = data[t]; // TODO: wrong
				if (data.find(t) == data.end())
				{
					t_data = data[t];
					t_data.g = INF;
					t_data.h = heur.estimate(operators, t, goal);
				}
				if (t_data.g > s_data.g + op.cost)
				{
					//frontier.erase(std::pair<Cost, State>(g[t] + h[t], t))
					t_data.g = s_data.g + op.cost;
					t_data.prev_state = s;
					t_data.prev_op = &op;
					t_data.iter = frontier.insert(
						std::pair<Cost, State>(t_data.g + t_data.h, t));
				}
			}
		}
		return start;
	}
};

int main()
{
	Problem p;
	p.atom_names.push_back("A");
	p.atom_names.push_back("B");
	Operator op;
	op.preconditions.push_back(true);
	op.preconditions.push_back(false);
	op.add_effects.push_back(false);
	op.add_effects.push_back(true);
	op.del_effects.push_back(true);
	op.del_effects.push_back(false);
	op.cost = 3;
	p.operators.push_back(op);
	State start, goal;
	start.push_back(true);
	start.push_back(false);
	goal.push_back(false);
	goal.push_back(true);
	Heuristic heur = HSP();
	std::cout << p.data[p.AStar(heur, start, goal)].g << std::endl;
}