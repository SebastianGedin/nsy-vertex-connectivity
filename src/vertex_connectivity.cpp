//============================================================================
// Name        : vertexconnectivity.cpp
// Author      : Sebastian Gedin
//============================================================================

#include <iostream>
#include <fstream>
#include <random>
#include <ctime>
#include <chrono>
#include <algorithm>
#include <boost/graph/copy.hpp>
#include <boost/graph/erdos_renyi_generator.hpp>
#include <boost/graph/adjacency_list.hpp>
#include <boost/graph/depth_first_search.hpp>
#include <boost/graph/random.hpp>
#include <boost/graph/edmonds_karp_max_flow.hpp>
#include <boost/graph/strong_components.hpp>

typedef boost::adjacency_list_traits<boost::vecS, boost::vecS,
		boost::bidirectionalS> Traits;
typedef boost::adjacency_list<boost::listS, boost::vecS, boost::bidirectionalS,
		boost::no_property,
		boost::property<boost::edge_capacity_t, long,
				boost::property<boost::edge_residual_capacity_t, long,
						boost::property<boost::edge_reverse_t,
								Traits::edge_descriptor>>>> DirectedGraph;
typedef boost::graph_traits<DirectedGraph>::edge_iterator EdgeIterator;
typedef boost::graph_traits<DirectedGraph>::vertex_iterator VertexIterator;
typedef boost::graph_traits<DirectedGraph>::vertex_descriptor Vertex;
typedef boost::graph_traits<DirectedGraph>::edge_descriptor Edge;

namespace util {

unsigned seed = std::chrono::system_clock::now().time_since_epoch().count();
std::default_random_engine generator(0);

bool with_probability(double p) {
	std::uniform_real_distribution<double> distribution(0.0, 1.0);
	return (distribution(generator) < p);
}

std::unordered_set<Vertex> get_out_neighbors(const DirectedGraph &g,
		std::unordered_set<Vertex> vertexSet) {
	std::unordered_set<Vertex> neighbors;
	for (Vertex u : vertexSet) {
		auto vpair = adjacent_vertices(u, g);
		for (auto vit = vpair.first; vit != vpair.second; ++vit) {
			if (vertexSet.count(*vit) == 0) {
				neighbors.insert(*vit);
			}
		}
	}
	return neighbors;
}

template<typename Container>
void print_container(Container &container) {
	std::string separator = " ";
	std::string sep = "";
	std::cout << "[";
	for (auto element : container) {
		std::cout << sep << element;
		sep = separator;
	}
	std::cout << "]" << std::endl;
}

void print_graph(const DirectedGraph &g) {
	auto vertexSet = boost::vertices(g);
	for (auto vit = vertexSet.first; vit != vertexSet.second; ++vit) {
		std::cout << *vit << ": ";
		auto neighbors = boost::adjacent_vertices(*vit, g);
		for (auto nit = neighbors.first; nit != neighbors.second; ++nit) {
			std::cout << *nit << " ";
		}
		std::cout << "\n";
	}
}

} // namespace util

namespace split {

DirectedGraph create_split_graph(const DirectedGraph &g, const Vertex &x) {
	DirectedGraph g_split;
	auto vpair = vertices(g);
	for (auto vi = vpair.first; vi != vpair.second; ++vi) {
		if (*vi != x) {
			add_edge(2 * (*vi), 1 + 2 * (*vi), g_split);
		}
	}

	typename boost::graph_traits<DirectedGraph>::edge_iterator ei, ei_end;
	for (boost::tie(ei, ei_end) = edges(g); ei != ei_end; ++ei) {
		Vertex s = source(*ei, g);
		Vertex t = target(*ei, g);
		if (s == x) {
			add_edge(2 * s, 2 * t, g_split);
		} else {
			add_edge(1 + 2 * s, 2 * t, g_split);
		}
	}

	return g_split;
}

std::unordered_set<Vertex> l_dash_to_l(std::unordered_set<Vertex> l_dash,
		Vertex x) {
	if (l_dash.empty()) {
		return {};
	}
	std::unordered_set<Vertex> l;
	for (Vertex v : l_dash) {
		if (v == (2 * x)) {
			l.insert(v / 2);
		} else if ((v % 2) == 0 && l_dash.count(v + 1)) {
			l.insert(v / 2);
		}
	}
	return l;
}

} //namespace split

/*
 * This namespace contains the code for the local vertex connectivity algorithm.
 */
namespace localvc {

void reverse_edge(Edge e, DirectedGraph &g) {
	add_edge(target(e, g), source(e, g), g);
	remove_edge(e, g);
}

void reverse_path(std::vector<Edge> path, DirectedGraph &g) {
	for (Edge e : path) {
		reverse_edge(e, g);
	}
}

std::unordered_set<Vertex> get_vertex_set(
		const std::unordered_map<Vertex, std::vector<Edge>> &paths) {
	std::unordered_set<Vertex> t;
	for (auto kv : paths) {
		t.insert(kv.first);
	}
	return t;
}

void dfs_util(const DirectedGraph &g, DirectedGraph &g_split, Edge e,
		std::unordered_map<Vertex, std::vector<Edge>> &paths,
		std::vector<Edge> &visited, int stop) {
	visited.push_back(e);

	Vertex s = source(e, g_split);
	Vertex t = target(e, g_split);

	if (paths.count(t) == 0) { // is tree edge

		if ((t % 2) == 0 && out_degree(t, g_split) == 0) { // is in-vertex and has not been split already
		// Split the vertex
			add_edge(t, t + 1, g_split);
			auto vpair = adjacent_vertices(t / 2, g);
			for (auto vi = vpair.first; vi != vpair.second; ++vi) {
				add_edge(t + 1, 2 * (*vi), g_split);
			}
		}

		// Add to paths
		std::vector<Edge> path(paths[s]);
		path.push_back(e);
		paths[t] = path;

		// Recurse
		auto epair = out_edges(t, g_split);
		for (auto ei = epair.first; ei != epair.second; ei++) {
			dfs_util(g, g_split, *ei, paths, visited, stop);
		}
	}

	if (visited.size() >= stop) { // stop reached
		throw 0;
	}

}

/*
 * Runs the local vertex connectivity algorithm for graph g, seed vertex x, volume v and looks for a cut of size less than k.
 */
std::unordered_set<Vertex> local_vertex_connectivity(const DirectedGraph &g,
		Vertex x, int v, int k) {
	double epsilon = 1.0 / (k + 0.00000001);
	int m = num_edges(g);
	int n = num_vertices(g);

	if (k < 1) {
		throw std::invalid_argument("Must have k >= 1");
	}
	if (epsilon <= 0 || epsilon > 1) {
		throw std::invalid_argument("Must have epsilon in range (0,1]");
	}
	if (v >= epsilon * m / 8.0) {
		throw std::invalid_argument("Invalid volume");
	}

	int stop = 8 * v / epsilon;

	DirectedGraph g_split;
	Vertex x_split = 2 * x;

	auto vpair = adjacent_vertices(x, g);
	for (auto vi = vpair.first; vi != vpair.second; ++vi) {
		add_edge(x_split, 2 * (*vi), g_split);
	}

	for (int i = 0; i < std::floor((1.0 + epsilon) * k); i++) {

		std::unordered_map<Vertex, std::vector<Edge>> paths;
		std::vector<Edge> visited;

		try {
			auto epair = out_edges(x_split, g_split);
			for (auto ei = epair.first; ei != epair.second; ei++) {
				dfs_util(g, g_split, *ei, paths, visited, stop);
			}

			std::unordered_set<Vertex> tree = get_vertex_set(paths);
			tree.insert(x);

			if (tree.empty()) {
				return {};
			}

			std::unordered_set<Vertex> l = split::l_dash_to_l(tree, x);
			std::unordered_set<Vertex> cut = util::get_out_neighbors(g, l);

			if (cut.size() + l.size() == num_vertices(g)) {
				return {};
			}

			return cut;

		} catch (int e) {
			if (e == 0 && (i + 1) < std::floor((1.0 + epsilon) * k)) {
				std::uniform_int_distribution<> distribution(0,
						visited.size() - 1);

				auto it = visited.begin();
				std::advance(it, distribution(util::generator));
				while (target(*it, g_split) == x_split) {
					it = visited.begin();
					std::advance(it, distribution(util::generator));
				}

				reverse_path(paths[target(*it, g)], g_split);
			}
		}
	}

	return {};
}
} // namespace localvc

/*
 * This namespace contains the code for creating a flow network from a graph and using Edmonds-Karp algorithm to find the min cut between two vertices.
 */
namespace maxflow {

std::unordered_set<Vertex> l_dash_to_l_flow(std::unordered_set<Vertex> l_dash,
		Vertex s) {
	if (l_dash.empty()) {
		return {};
	}
	std::unordered_set<Vertex> l;
	for (Vertex v : l_dash) {
		if (v == (2 * s)) {
			l.insert(v / 2);
		} else if ((v % 2) == 0 && l_dash.count(v + 1)) {
			l.insert(v / 2);
		}
	}
	return l;
}

/*
 * Returns the minimum vertex cut set between vertices s and t in g and the size of that cut.
 */
std::pair<std::unordered_set<Vertex>, long> max_flow(const DirectedGraph &g,
		Vertex s, Vertex t) {
	auto npair = adjacent_vertices(s, g);
	for (auto vi = npair.first; vi != npair.second; ++vi) {
		if ((*vi) == t) {
			std::unordered_set<Vertex> empty;
			return std::make_pair(empty, LLONG_MAX);
		}
	}

	DirectedGraph g_flow;
	boost::property_map<DirectedGraph, boost::edge_capacity_t>::type capacityMap =
			get(boost::edge_capacity, g_flow);
	boost::property_map<DirectedGraph, boost::edge_reverse_t>::type revMap =
			get(boost::edge_reverse, g_flow);

	auto vpair = vertices(g);
	for (auto vi = vpair.first; vi != vpair.second; ++vi) {
		if (*vi != s && *vi != t) {
			Edge e1, e2;
			bool in1, in2;
			boost::tie(e1, in1) = add_edge(2 * (*vi), 1 + 2 * (*vi), g_flow);
			boost::tie(e2, in2) = add_edge(1 + 2 * (*vi), 2 * (*vi), g_flow);
			capacityMap[e1] = 1;
			capacityMap[e2] = 0;
			revMap[e1] = e2;
			revMap[e2] = e1;
		}
	}

	EdgeIterator ei, ei_end;
	for (boost::tie(ei, ei_end) = edges(g); ei != ei_end; ++ei) {
		Vertex v1 = boost::source(*ei, g);
		Vertex v2 = boost::target(*ei, g);
		Edge e1, e2;
		bool in1, in2;
		if (v1 == s || v1 == t) {
			boost::tie(e1, in1) = add_edge(2 * v1, 2 * v2, g_flow);
			boost::tie(e2, in2) = add_edge(2 * v2, 2 * v1, g_flow);
		} else {
			boost::tie(e1, in1) = add_edge(1 + 2 * v1, 2 * v2, g_flow);
			boost::tie(e2, in2) = add_edge(2 * v2, 1 + 2 * v1, g_flow);
		}
		capacityMap[e1] = 1;
		capacityMap[e2] = 0;
		revMap[e1] = e2;
		revMap[e2] = e1;
	}

	boost::property_map<DirectedGraph, boost::edge_residual_capacity_t>::type resCapacityMap =
			get(boost::edge_residual_capacity, g_flow);
	std::vector<boost::default_color_type> color(num_vertices(g_flow));
	std::vector<Traits::edge_descriptor> pred(num_vertices(g_flow));

	long flow = edmonds_karp_max_flow(g_flow, 2 * s, 2 * t, capacityMap,
			resCapacityMap, revMap, &color[0], &pred[0]);

	std::unordered_set<Vertex> part;
	auto vpair_g_flow = vertices(g_flow);
	for (auto vit = vpair_g_flow.first; vit != vpair_g_flow.second; ++vit) {
		if (color[*vit] == 4) {
			part.insert(*vit);
		}
	}

	part = l_dash_to_l_flow(part, s);

	std::unordered_set<Vertex> cut = util::get_out_neighbors(g, part);

	return std::make_pair(cut, flow);
}

} //namespace maxflow

namespace algorithm {

/*
 * The random max-flow algorithm. Looks for a cut smaller than k.
 */
std::unordered_set<Vertex> random_max_flow(const DirectedGraph &g, int k) {
	auto t1 = std::chrono::high_resolution_clock::now();
	double a = std::pow(num_edges(g) * 1.0, 1.0 / 3.0);

	while (true) {
		Vertex v1 = random_vertex(g, util::generator);
		Vertex v2 = random_vertex(g, util::generator);
		while (v1 == v2) {
			v2 = random_vertex(g, util::generator);
		}

		std::pair<std::unordered_set<Vertex>, long> maxFlowResult =
				maxflow::max_flow(g, v1, v2);
		long flow = maxFlowResult.second;
		if (flow < k) {
			return maxFlowResult.first;
		}
	}

	return {};
}

int num_digits(int n) {
	int digits = 0;
	while (n) {
		n /= 10;
		digits++;
	}
	return digits;
}

/*
 * The local algorithm. Looks for a cut smaller than k.
 */
std::unordered_set<Vertex> local(const DirectedGraph &g, int k) {
	auto t1 = std::chrono::high_resolution_clock::now();
	double a = std::pow(num_edges(g) * 1.0, 1.0 / 3.0);
	DirectedGraph g_rev;
	boost::copy_graph(boost::make_reverse_graph<DirectedGraph>(g), g_rev);

	int d = num_digits(a) - 1;

	std::unordered_set<Vertex> cut;

	while (true) {
		for (int j = 0; j < 100 * pow(10, d) * 10; j++) {
			for (int s = 2; s <= a; s *= 2) {
				int numberOfSamples = ceil(num_vertices(g) / (pow(10, d) * s));
				int v = s;
				for (int j = 0; j < numberOfSamples; j++) {

					Vertex x = random_vertex(g, util::generator);

					try {
						std::unordered_set<Vertex> cut =
								localvc::local_vertex_connectivity(g, x, v, k);
						if (!cut.empty()) {
							return cut;
						}
						cut = localvc::local_vertex_connectivity(g_rev, x, v,
								k);
						if (!cut.empty()) {
							return cut;
						}
					} catch (std::invalid_argument &e) {
						return {};
					}
				}
			}
		}
	}

	return {};
}

/*
 * The naive algorithm. Looks for a cut smaller than k.
 */
std::unordered_set<Vertex> naive(const DirectedGraph &g, int k) {
	auto t1 = std::chrono::high_resolution_clock::now();
	long n = num_vertices(g);
	std::vector<int> index_vector;
	for (long i = 0; i < n; i++) {
		index_vector.push_back(i);
	}
	std::random_shuffle(index_vector.begin(), index_vector.end());
	for (auto vit1 = index_vector.begin(); vit1 != index_vector.end(); ++vit1) {
		for (auto vit2 = index_vector.begin(); vit2 != index_vector.end();
				++vit2) {
			if (vit1 != vit2) {
				std::pair<std::unordered_set<Vertex>, long> max_flow_result =
						maxflow::max_flow(g, *vit1, *vit2);
				long flow = max_flow_result.second;
				if (flow < k) {
					return max_flow_result.first;
				}
			}
		}
	}
	return {};
}

} // namespace algorithm

namespace graphgen {

void add_random_edges(DirectedGraph &g, int from, int d, int start_index,
		int end_index) {
	std::vector<int> index_vector;
	for (long i = start_index; i < end_index; i++) {
		if (i != from) {
			index_vector.push_back(i);
		}
	}
	std::random_shuffle(index_vector.begin(), index_vector.end());

	for (int i = 0; i < d && i < index_vector.size(); i++) {
		int to = index_vector[i];
		add_edge(from, to, g);
	}
}

DirectedGraph create_regular_cut_graph(int n_l, int n_s, int n_r, int d) {
	DirectedGraph g;
	int n = n_l + n_s + n_r;

	// Edges from L to L or S
	for (int from = 0; from < n_l; from++) {
		add_random_edges(g, from, d, 0, n_l + n_s);
	}

	// Edges from R to R or S
	for (int from = n_l + n_s; from < n; from++) {
		add_random_edges(g, from, d, n_l, n);
	}

	// Edges from S to L, S or R
	for (int from = n_l; from < n_l + n_s; from++) {
		add_random_edges(g, from, d, 0, n);
	}

	// Edges to S from R and L
	for (int v = n_l; v < n_l + n_s; v++) {
		if (!edge(0, v, g).second) {
			add_edge(0, v, g);
		}
		if (!edge(v, 0, g).second) {
			add_edge(v, 0, g);
		}
		if (!edge(n_s + n_l, v, g).second) {
			add_edge(n_s + n_l, v, g);
		}
		if (!edge(v, n_s + n_l, g).second) {
			add_edge(v, n_s + n_l, g);
		}
	}

	// Edges from S to L and R (to ensure connected)
	for (int from = n_l; from < n_l + n_s; from++) {
		if (!edge(from, 0, g).second) {
			add_edge(from, 0, g);
		}
	}

	return g;
}

} // namespace graphgen

int main(int argc, char **argv) {

	// Example of creating a graph with a vertex cut (L, S, R) and degree parameter d and running each algorithm on it.

	int l_size = 1;
	int s_size = 2;
	int r_size = 200;
	int d = 15;

	DirectedGraph g = graphgen::create_regular_cut_graph(l_size, s_size, r_size,
			d);

	std::unordered_set<Vertex> local_cut = algorithm::local(g, s_size + 1);
	std::cout << "Local algorithm found cut: ";
	util::print_container(local_cut);

	std::unordered_set<Vertex> random_maxflow_cut = algorithm::random_max_flow(
			g, s_size + 1);
	std::cout << "Random max-flow algorithm found cut: ";
	util::print_container(random_maxflow_cut);

	std::unordered_set<Vertex> naive_cut = algorithm::naive(g, s_size + 1);
	std::cout << "Naive algorithm found cut: ";
	util::print_container(naive_cut);

	return 0;
}
