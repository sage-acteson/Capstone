# This file is part of Toboggan, https://github.com/TheoryInPractice/Toboggan/,
# and is Copyright (C) North Carolina State University, 2017. It is licensed
# under the three-clause BSD license; see LICENSE.
#
import copy
import math
import queue
import time
import numpy as np
from collections import defaultdict
from itertools import permutations
import random
from ortools.graph import pywrapgraph


class IfdAdjList:
    def __init__(self, graph_file=None, graph_number=None, name=None,
                 num_nodes=None):
        self.graph_file = graph_file
        self.graph_number = graph_number
        self.name = name
        self.num_nodes_at_start = num_nodes
        self.vertices = set()
        self.adj_list = defaultdict(list)
        self.inverse_adj_list = defaultdict(list)
        self.out_arcs_lists = defaultdict(list)
        self.in_arcs_lists = defaultdict(list)
        self.arc_info = defaultdict(list)
        self.max_arc_label = 0
        self.paths = []
        self.weights = []
        self.splices = 0
        self.rebalances = 0
        self.overlap_count = 0
        self.interval_udpates = 0
        self.pairwise_rebalances = 0
        self.pairwise_splices = 0
        self.mapping = dict()  # for storing how to undo reduction

    def get_arc(self, start, destin):
        for arc in self.arc_info.keys():
            if self.arc_info[arc]["start"] == start \
                        and self.arc_info[arc]["destin"] == destin:
                return arc

    def set_paths(self, paths):
        """Set self.paths (for testing)."""
        self.paths = paths

    def count_paths_with_zero_intervals(self):
        """Return the number of paths in the current solution with at least one
        edge with an interval of zero."""
        zeros = []
        for path in self.paths:
            # print("Checking path {}".format(path))
            has_zero = 0
            for arc in path:
                # lb = self.arc_info[arc]["lower_bound"]
                # ub = self.arc_info[arc]["upper_bound"]
                # print("{} {} interval".format(lb,ub))
                if (self.arc_info[arc]["upper_bound"] -
                        self.arc_info[arc]["lower_bound"]) == 0:
                    has_zero = 1
            zeros.append(has_zero)
        print(zeros)
        return(sum(zeros))

    def update_edge_weights(self):
        """Update edge weights based on weights of paths."""
        # set all weights to 0
        for arc in self.arc_info.keys():
            self.arc_info[arc]["weight"] = 0
        # iterate through all paths and add weights to arcs
        for (path, weight) in zip(self.paths, self.weights):
            for arc in path:
                # Count this path's flow toward the arc's total
                self.arc_info[arc]["weight"] = self.arc_info[arc]["weight"] + \
                                                        weight

    def check_conservation_of_flow(self):
        """Check that conservation of flow is satisfied by current flow."""
        # for all vertices except first and last (s and t)
        for vert in self.vertices:
            if vert == self.sink() or vert == self.source():
                continue
            # check conservation of flow
            flow_in = 0
            for in_arc in self.in_arcs_lists[vert]:
                flow_in += self.arc_info[in_arc]["weight"]
            flow_out = 0
            for out_arc in self.out_arcs_lists[vert]:
                flow_out += self.arc_info[out_arc]["weight"]
            # print("For vert {}, flow in is {} and flow out is {}".format(
            #     vert, flow_in, flow_out))
            assert (flow_in == flow_out), "Conservation of flow violated"

    def add_new_source_sink(self):
        """Remove current source and sink and add new ones with edges to all
        verts and give all new edges [0, inf] bounds."""
        source = self.source()
        sink = self.sink()
        for arc in self.out_arcs_lists[source]:
            self.arc_info[arc]["lower_bound"] = 0
            self.arc_info[arc]["upper_bound"] = float('inf')
        for arc in self.in_arcs_lists[sink]:
            self.arc_info[arc]["lower_bound"] = 0
            self.arc_info[arc]["upper_bound"] = float('inf')
        for vert in self.vertices:
            if vert != source and vert != sink:
                if self.get_arc(source, vert) is None:
                    self.add_inexact_edge(source, vert, 0, float('inf'))
                if self.get_arc(vert, sink) is None:
                    self.add_inexact_edge(vert, sink, 0, float('inf'))

    def check_flow(self):
        """Check that the set of paths  satisfies bounds."""
        # make a total_flow key in the arc_info dictionary and initialize to 0
        for arc in self.arc_info.keys():
            self.arc_info[arc]["total_flow"] = 0
        # print("#  Final paths and weights are:")
        index = 0
        for (path, weight) in zip(self.paths, self.weights):
            # print("#\tPath {}: {}. Weight: {}.".format(index, path, weight))
            index = index + 1
            for arc in path:
                # Count this path's flow toward the arc's total
                self.arc_info[arc]["total_flow"] =\
                    self.arc_info[arc]["total_flow"] + weight
        for arc in self.arc_info.keys():
            f = self.arc_info[arc]["total_flow"]
            lb = self.arc_info[arc]["lower_bound"]
            ub = self.arc_info[arc]["upper_bound"]
            # print("#\tFor arc {}: flow={}, bounds = [{},{}]".format(
            #     arc, f, lb, ub))
            assert (f >= lb), "Flow value less than lower bound"
            assert (f <= ub), "Flow value greater than upper bound"

    def check_paths(self):
        """Check that paths are valid."""
        for path in self.paths:
            # check that arc starts at s
            arc = path[0]
            arc_start = self.arc_info[arc]["start"]
            assert(arc_start == self.source()), "Path does not start at s"
            # check that internal arcs are valid
            for (i, arc) in enumerate(path[:-1]):
                next_arc = path[i + 1]
                arc_destin = self.arc_info[arc]["destin"]
                next_arc_start = self.arc_info[next_arc]["start"]
                assert (arc_destin == next_arc_start), "Invalid path"
            arc = path[-1]
            arc_end = self.arc_info[arc]["destin"]
            assert(arc_end == self.sink()), "Path does not end at t"

    def convert_paths(self):
        """Convert paths in the ifd graph to node sequences (instead of edge
        sequences), and then to nodes in the original graph."""
        # convert to node sequences, dropping s'
        self.nodeseq_paths = []
        for path in self.paths:
            node_seq = []  # don't include s'
            for arc in path:
                node_seq.append(self.arc_info[arc]['destin'])
            self.nodeseq_paths.append(node_seq)
        # convert to og graph
        self.converted_paths = []
        for path in self.nodeseq_paths:
            this_path = []
            add_next_node = True
            for i in range(len(path) - 1):
                print("This path is", this_path)
                node1 = path[i]
                node2 = path[i + 1]
                print("node1={}, node2={}".format(node1, node2))
                if (node1, node2) in self.mapping:
                    sc = self.mapping[(node1, node2)]
                    print("uses sc edge for {}".format(sc))
                    print("should add {}, but also need to check for overlaps".
                          format(sc[1:-1]))
                    if sc[1] in this_path:
                        # we have an overlap
                        start = len(this_path) - this_path.index(sc[1])
                        this_path.extend(sc[start:-1])
                    else:
                        this_path.extend(sc[1:-1])
                    add_next_node = False  # next node is second of sc edge
                elif add_next_node:
                    this_path.append(node1)
                else:
                    add_next_node = True
            this_path.append(path[-1])
            self.converted_paths.append(this_path)

    def get_converted_paths(self):
        return self.converted_paths

    def get_paths(self):
        """Get the set of paths"""
        return self.paths

    def get_weights(self):
        """Get the set of weights"""
        return self.weights

    def add_error_paths(self, num, weight):
        print("Adding paths.")

        def add_s_t_path(weight):
            print("Adding a new path with weight {}".format(weight))
            s = min(self.vertices)
            t = max(self.vertices)
            current_node = s
            print("Node: {}".format(current_node))
            while current_node is not t:
                out_arcs = self.out_arcs_lists[current_node]
                random_arc = random.choice(out_arcs)
                # update weight of this arc
                self.arc_info[random_arc]["weight"] += weight
                # update current node
                current_node = self.arc_info[random_arc]["destin"]
                print("Node: {}".format(current_node))

        for x in range(num):
            add_s_t_path(weight)

    def write_exact_graph_to_file(self, output_file):
        """Write exact graph to file."""
        print("Writing output file.")
        with open(output_file, 'w') as f:
            f.write("# graph number = 0 name = interval_graph\n")
            f.write(str(len(self.vertices)) + "\n")
            for node in self.vertices:
                for arc in self.out_arcs_lists[node]:
                    s = self.arc_info[arc]['start']
                    t = self.arc_info[arc]['destin']
                    w = self.arc_info[arc]['weight']
                    f.write("{} {} {}\n".format(s, t, w))

    def get_num_zero_lower_bounds(self):
        count = 0
        for arc in self.arc_info.keys():
            if self.arc_info[arc]["lower_bound"] == 0:
                count += 1
        return(count)

    def get_splices(self):
        return(self.splices)

    def get_overlap_count(self):
        return(self.overlap_count)

    def get_rebalances(self):
        return(self.rebalances)

    def get_pairwise_rebalances(self):
        return self.pairwise_rebalances

    def get_pairwise_splices(self):
        return self.pairwise_splices

    def get_interval_updates(self):
        return(self.interval_updates)

    def get_k(self):
        return(len(self.paths))

    def get_edge_info(self):
        edge_info = []
        for arc in self.arc_info.keys():
            start = self.arc_info[arc]["start"]
            destin = self.arc_info[arc]["destin"]
            lb = self.arc_info[arc]["lower_bound"]
            ub = self.arc_info[arc]["upper_bound"]
            info = (start, destin, lb, ub)
            edge_info.append(info)
        return(edge_info)

    def get_edge_weight(self, start, destin):
        arc = self.get_arc(start, destin)
        return self.arc_info[arc]["weight"]

    def get_edge_bounds(self, start, destin):
        arc = self.get_arc(start, destin)
        return (self.arc_info[arc]["lower_bound"],
                self.arc_info[arc]["upper_bound"])

    def create_queue(self):
        # for each arc with lb =0 and f>0, prioritize by current flow value
        q = queue.PriorityQueue()
        for arc in self.arc_info.keys():
            lb = self.arc_info[arc]["lower_bound"]
            f = self.arc_info[arc]["weight"]
            if (lb == 0) & (f > 0):
                # print("Adding {},{} to the queue".format(f, arc))
                q.put(([f, arc]))
        return(q)

    def run_heuristic_1(self):
        """Modify initial flow to remove edges, if possible."""

        # store original upper bounds
        for arc in self.arc_info.keys():
            self.arc_info[arc]["original_ub"] =\
                self.arc_info[arc]["upper_bound"]

        q = self.create_queue()
        updates = 0

        while (not q.empty()):
            # for every edge that has flow 0, set upper bound to 0
            # this ensures that we don't add an edge to remove this one
            for arc in self.arc_info.keys():
                if self.arc_info[arc]["weight"] == 0:
                    self.arc_info[arc]["upper_bound"] = 0

            arc_id = q.get()[1]
            # print("Trying to adjust flow using arc {}".format(arc_id))
            # set upper bound of this edge to 0
            self.arc_info[arc_id]["upper_bound"] = 0
            flow_found = self.update_flow()
            if flow_found:
                # start = self.arc_info[arc_id]["start"]
                # destin = self.arc_info[arc_id]["destin"]
                # print("Found flow without arc {}, ({},{}).".format(arc_id,
                #    start, destin))
                # create new queue from new flow
                q = self.create_queue()
                updates += 1

        # return bounds to original
        for arc in self.arc_info.keys():
            self.arc_info[arc]["upper_bound"] =\
                self.arc_info[arc]["original_ub"]
        return(updates)

    def unexplained_flow(self):
        flows = [self.arc_info[arc]["unexplained_flow"]
                 for arc in self.arc_info]
        return(sum(flows) > 0)

    def run_greedy_width(self):
        """
        Find a greedy-width solution for the given flow graph.
        """
        print("\nRunning greedy width to find an initial path solution.")
        for arc in self.arc_info:
            self.arc_info[arc]["unexplained_flow"] =\
                self.arc_info[arc]["weight"]
        tries = 0
        while self.unexplained_flow():
            tries += 1
            # don't keep going forever
            assert tries < 1000
            self.run_dijkstra()

    # from https://startupnextdoor.com/dijkstras-algorithm-in-python-3/
    def run_dijkstra(self):
        q = queue.PriorityQueue()
        parents = dict()
        widths = dict()
        start_weight = 0
        source = self.source()
        dest = self.sink()

        for v in self.vertices:
            weight = start_weight
            if v == source:
                weight = float("inf")
            widths[v] = weight
            parents[v] = None

        q.put(([0, source]))

        while not q.empty():
            v_tuple = q.get()
            v = v_tuple[1]
            for e in self.out_arcs_lists[v]:
                weight = self.arc_info[e]["unexplained_flow"]
                e_dest = self.arc_info[e]["destin"]
                current_min_width = widths[e_dest]
                width_to_v = widths[v]
                candidate_min_width = min(width_to_v, weight)
                if current_min_width < candidate_min_width:
                    widths[e_dest] = candidate_min_width
                    parents[e_dest] = e
                    q.put(([widths[e_dest], e_dest]))

        shortest_path = []
        edge = parents[dest]
        while edge is not None:
            shortest_path.append(edge)
            previous_vertex = self.arc_info[edge]["start"]
            edge = parents[previous_vertex]

        flow = widths[dest]
        shortest_path.reverse()
        for edge in shortest_path:
            self.arc_info[edge]["unexplained_flow"] -= flow
        self.paths.append(shortest_path)
        print(shortest_path)
        self.weights.append(flow)

    def set_weights(self, weights):
        self.weights = weights

    def add_edge(self, u, v, flow):
        self.vertices.add(u)
        self.vertices.add(v)
        self.adj_list[u].append((v, flow))
        self.inverse_adj_list[v].append((u, flow))

        this_label = self.max_arc_label
        self.arc_info[this_label] = {
                                    'start': u,
                                    'destin': v,
                                    'weight': flow,
        }
        self.out_arcs_lists[u].append(this_label)
        self.in_arcs_lists[v].append(this_label)
        self.max_arc_label += 1

    def add_inexact_edge(self, u, v, lb, ub):
        self.vertices.add(u)
        self.vertices.add(v)
        # give 0 flow
        flow = 0
        self.adj_list[u].append((v, flow))
        self.inverse_adj_list[v].append((u, flow))

        this_label = self.max_arc_label
        self.arc_info[this_label] = {
                                    'start': u,
                                    'destin': v,
                                    'weight': flow,
                                    'lower_bound': lb,
                                    'upper_bound': ub
        }
        self.out_arcs_lists[u].append(this_label)
        self.in_arcs_lists[v].append(this_label)
        self.max_arc_label += 1

    def out_arcs(self, node):
        return self.out_arcs_lists[node]

    def in_arcs(self, node):
        return self.in_arcs_lists[node]

    def arcs(self):
        return self.arc_info.items()

    def __len__(self):
        return len(self.vertices)

    def __iter__(self):
        return iter(self.vertices)

    def source(self):
        for v in self:
            if self.in_degree(v) == 0:
                return v
        raise TypeError("This graph has no source")

    def sink(self):
        for v in self:
            if self.out_degree(v) == 0:
                return v
        raise TypeError("This graph has no sink")

    def labeled_neighborhood(self, u):
        if u in self.adj_list:
            res = []
            for arc in self.out_arcs_lists[u]:
                dest = self.arc_info[arc]['destin']
                flow = self.arc_info[arc]['weight']
                res.append([dest, flow, arc])
            return res
        else:
            return []

    def neighborhood(self, u):
        if u in self.adj_list:
            return self.adj_list[u]
        else:
            return []

    def out_neighborhood(self, u):
        return self.neighborhood(u)

    def in_neighborhood(self, u):
        if u in self.inverse_adj_list:
            return self.inverse_adj_list[u]
        else:
            return []

    def copy(self):
        res = IfdAdjList(self.graph_file, self.graph_number, self.name,
                         len(self))
        res.adj_list = copy.deepcopy(self.adj_list)
        res.inverse_adj_list = copy.deepcopy(self.inverse_adj_list)
        res.out_arcs_lists = copy.deepcopy(self.out_arcs_lists)
        res.in_arcs_lists = copy.deepcopy(self.in_arcs_lists)
        res.arc_info = copy.deepcopy(self.arc_info)
        res.vertices = set(self.vertices)
        return res

    def edges(self):
        for u in self.adj_list:
            for (v, flow) in self.adj_list[u]:
                yield (u, v, flow)

    def arc_id(self, u, v):
        """Return the arc_id of a edge between two nodes. Throws exception if
        there is more than one arc_id between two edges, so should not be used
        on reduced graphs."""
        arcs = []
        for arc, info in self.arc_info.items():
            if info["start"] == u and info["destin"] == v:
                arcs.append(arc)
        if len(arcs) > 1:
            raise TypeError("This graph has multiple edges between {} and {}".
                            format(u, v))
        else:
            return arcs[0] if len(arcs) == 1 else None

    def num_edges(self):
        return sum(1 for _ in self.edges())

    def out_degree(self, v):
        return len(self.out_neighborhood(v))

    def in_degree(self, v):
        return len(self.in_neighborhood(v))

    def contracted(self):
        """
        Return a copy of the graph in which all uv arcs where u has out degree
        1 or v has in degree 1 are contracted.
        """
        res = self.copy()
        # remembering which arcs were contracted in order to reconstruct the
        # paths in the original graph later
        arc_mapping = {e: [e] for e, _ in res.arcs()}
        # contract out degree 1 vertices
        for u in list(res):
            if res.out_degree(u) == 1:
                arc = res.out_arcs(u)[0]
                # mark u's inarcs to know they use the arc to be contracted
                for a in res.in_arcs(u):
                    arc_mapping[a].extend(arc_mapping[arc])
                # if u is the source, it has no in-arcs to mark the
                # contraction of this out-arc, so we store it in the out-arcs
                # of its out-neighbor.
                if res.in_degree(u) == 0:
                    v = res.out_neighborhood(u)[0][0]
                    for a in res.out_arcs(v):
                        new_path = list(arc_mapping[arc])
                        new_path.extend(arc_mapping[a])
                        arc_mapping[a] = new_path

                # contract the edge
                res.contract_edge(arc, keep_source=False)
        # contract in degree 1 vertices
        for v in list(res):
            if res.in_degree(v) == 1:
                arc = res.in_arcs(v)[0]
                # mark v's outarcs to know they use the arc to be contracted
                for a in res.out_arcs(v):
                    new_path = list(arc_mapping[arc])
                    new_path.extend(arc_mapping[a])
                    arc_mapping[a] = new_path
                # if u is the sink, it has no out-arcs to mark the contraction
                # of this in-arc, so we store it in the in-arcs of its
                # in-neighbor.
                if res.out_degree(v) == 0:
                    u = res.in_neighborhood(v)[0][0]
                    for a in res.in_arcs(u):
                        arc_mapping[a].extend(arc_mapping)

                # print("{} has in degree 1 from {}".format(v,u))
                res.contract_edge(arc, keep_source=True)
        return res, arc_mapping

    def contract_edge(self, e, keep_source=True):
        """
        Contract the arc e.

        If keep_source is true, the resulting vertex retains the label of the
        source, otherwise it keeps the sink's
        """
        u = self.arc_info[e]["start"]
        v = self.arc_info[e]["destin"]
        w = self.arc_info[e]["weight"]

        i = self.out_arcs(u).index(e)
        j = self.in_arcs(v).index(e)

        # move last neighbor into position of uv arc and delete arc
        self.adj_list[u][i] = self.adj_list[u][-1]
        self.adj_list[u] = self.adj_list[u][:-1]
        self.out_arcs_lists[u][i] = self.out_arcs_lists[u][-1]
        self.out_arcs_lists[u] = self.out_arcs_lists[u][:-1]

        # move last neighbor into position of uv arc and delete arc
        self.inverse_adj_list[v][j] = self.inverse_adj_list[v][-1]
        self.inverse_adj_list[v] = self.inverse_adj_list[v][:-1]
        self.in_arcs_lists[v][j] = self.in_arcs_lists[v][-1]
        self.in_arcs_lists[v] = self.in_arcs_lists[v][:-1]

        # to keep things concise, use the label a for the vertex to keep
        # and label b for the vertex to discard
        a, b = (u, v) if keep_source else (v, u)

        # update out-neighbors of a
        self.adj_list[a].extend(self.out_neighborhood(b))
        self.out_arcs_lists[a].extend(self.out_arcs_lists[b])
        # make out-neighbors of b point back to a
        for lab, edge in zip(self.out_arcs(b), self.out_neighborhood(b)):
            w, f = edge
            i = self.inverse_adj_list[w].index((b, f))
            self.arc_info[lab]["start"] = a
            self.inverse_adj_list[w][i] = (a, f)

        # update in-neighbors of a
        self.inverse_adj_list[a].extend(self.in_neighborhood(b))
        self.in_arcs_lists[a].extend(self.in_arcs_lists[b])
        # make in neighbors of b point to a
        for lab, edge in zip(self.in_arcs(b), self.in_neighborhood(b)):
            w, f = edge
            i = self.adj_list[w].index((b, f))
            self.arc_info[lab]["destin"] = a
            self.adj_list[w][i] = (a, f)

        if b in self.adj_list:
            del self.adj_list[b]
        if b in self.inverse_adj_list:
            del self.inverse_adj_list[b]
        self.vertices.remove(b)
        del self.arc_info[e]

    def show(self):
        import networkx as nx
        import matplotlib.pyplot as plt
        G = nx.DiGraph()
        for u, w, f in self.edges():
            G.add_edge(u, w)
        nx.draw(G)
        plt.show()

    def write_graphviz(self, filename):
        f = open(filename, "w")
        f.write("digraph G {\n")
        f.write("rankdir=LR;\n")
        for u, v, _ in self.edges():
            arc = self.arc_id(u, v)
            lb = self.arc_info[arc]["lower_bound"]
            ub = self.arc_info[arc]["upper_bound"]
            f.write("{} -> {} [ label = \"[{},{}]\" ];\n".format(u, v, lb, ub))
        f.write("}")
        f.close()

    def write_graph_to_file(self, filename):
        """Write interval graph to file."""
        with open(filename, 'w') as f:
            f.write("# graph number = 0 name = interval_graph\n")
            f.write(str(len(self.vertices)) + "\n")
            for node in self.vertices:
                for arc in self.out_arcs_lists[node]:
                    s = self.arc_info[arc]['start']
                    t = self.arc_info[arc]['destin']
                    w = self.arc_info[arc]['weight']
                    lb = self.arc_info[arc]['lower_bound']
                    ub = self.arc_info[arc]['upper_bound']
                    f.write("{} {} {} {} {} {}\n".format(s, t, w, lb, ub, arc))

    def print_out_unexplained(self):
        """Print the graph to screen."""
        for node in self.vertices:
            for arc in self.out_arcs_lists[node]:
                s = self.arc_info[arc]['start']
                t = self.arc_info[arc]['destin']
                w = self.arc_info[arc]['unexplained_flow']
                print("({} {}) unexplained flow={}, edgeId={}".format(s, t, w,
                                                                      arc))

    def print_out(self):
        """Print the graph to screen."""
        for node in self.vertices:
            for arc in self.out_arcs_lists[node]:
                s = self.arc_info[arc]['start']
                t = self.arc_info[arc]['destin']
                w = self.arc_info[arc]['weight']
                lb = self.arc_info[arc]['lower_bound']
                u = self.arc_info[arc]['upper_bound']
                print("{} {} {} {} flow={}, edgeId={}".format(s, t, lb, u, w,
                                                              arc))

    def find_B(self):
        """Find maximum upper bound from lower bounds."""
        max_lb = 0
        for arc in self.arcs():
            lb = self.arc_info[arc[0]]['lower_bound']
            max_lb = max(max_lb, lb)
        n = len(self)
        m = len(list(self.edges()))
        return((m - n + 2)*max_lb)

    def update_upper_bounds(self, B):
        """Set any infinite upper bound to B"""
        for arc in self.arcs():
            if self.arc_info[arc[0]]['upper_bound'] == -1:
                self.arc_info[arc[0]]['upper_bound'] = B

    def print_paths(self):
        print("#  Paths are: {}".format(self.paths))
        print("#  Weights are: {}\n".format(self.weights))

    def get_interval_from_minflow(self, wide=False):
        """Use the minflow approach from Traph to find intervals."""
        start_nodes = []
        end_nodes = []
        capacities = []
        unit_costs = []
        A = 0
        s_prime = self.sink() + 1
        t_prime = self.sink() + 2
        x = self.sink() + 3
        # for every edge in the graph, add edge to mincost flow instance with
        # infinite capacity and cost 1
        # also add backwards edge
        for arc in self.arc_info.keys():
            # forward edge
            start_nodes.append(self.arc_info[arc]["start"])
            end_nodes.append(self.arc_info[arc]["destin"])
            capacities.append(100000)  # capacity of 100,000 instead of inf
            unit_costs.append(1)
            # print("Adding arc ({}, {}) with unit cost and cap inf".format(
            #    self.arc_info[arc]["start"],
            #    self.arc_info[arc]["destin"]))
            # backward edge
            start_nodes.append(self.arc_info[arc]["destin"])
            end_nodes.append(self.arc_info[arc]["start"])
            capacities.append(int(self.arc_info[arc]["weight"]))  # no negative
            unit_costs.append(1)
            # print("Adding arc ({}, {}) with unit cost and cap inf".format(
            #    self.arc_info[arc]["destin"],
            #    self.arc_info[arc]["start"]))
        # add (x,s) and (t,x) edges with same cap, cost as above
        in_weight_x = 0
        for in_arc in self.in_arcs_lists[self.sink()]:
            in_weight_x += self.arc_info[in_arc]["weight"]
        out_weight_x = 0
        for out_arc in self.out_arcs_lists[self.source()]:
            out_weight_x += self.arc_info[out_arc]["weight"]
        # (x,s)
        start_nodes.append(x)
        end_nodes.append(self.source())
        capacities.append(100000)  # capacity of 100,000 instead of inf
        unit_costs.append(1)
        # print("Adding arc ({}, {}) with unit cost and cap inf".format(
        #    x,
        #    self.source()))
        # backward
        start_nodes.append(self.source())
        end_nodes.append(x)
        capacities.append(int(out_weight_x))  # don't go negative
        unit_costs.append(1)
        # print("Adding arc ({}, {}) with unit cost and cap inf".format(
        #    self.source(),
        #    x))
        # (t,x)
        start_nodes.append(self.sink())
        end_nodes.append(x)
        capacities.append(100000)  # capacity of 100,000 instead of inf
        unit_costs.append(1)
        # print("Adding arc ({}, {}) with unit cost and cap inf".format(
        #    self.sink(),
        #    x))
        # backward
        start_nodes.append(x)
        end_nodes.append(self.sink())
        capacities.append(int(in_weight_x))  # don't go negative
        unit_costs.append(1)
        # print("Adding arc ({}, {}) with unit cost and cap inf".format(
        #    x,
        #    self.sink()))
        # for all verts, if a-exc < 0, add edge (s', v) with capacity -a-exc(v)
        # and cost 0, and if a-exc > 0, add edge (v, t') with capacity a-exc(v)
        # and cost 0.
        for v in self:
            # process internal verts only, since we assume source and sink have
            # no in and out edges respectively
            if v != self.source() and v != self.sink():
                # compute a-exc(v)
                in_weight = 0
                for in_arc in self.in_arcs_lists[v]:
                    in_weight += self.arc_info[in_arc]["weight"]
                out_weight = 0
                for out_arc in self.out_arcs_lists[v]:
                    out_weight += self.arc_info[out_arc]["weight"]
                a_exc = out_weight - in_weight
                if a_exc < 0:
                    # add edge (s', v)
                    start_nodes.append(s_prime)
                    end_nodes.append(v)
                    capacities.append(int(-a_exc))
                    unit_costs.append(0)
                    # print("Adding arc ({}, {}) with cost 0 and cap {}".
                    #       format(s_prime, v, int(-a_exc)))
                if a_exc > 0:
                    # add edge (v, t')
                    start_nodes.append(v)
                    end_nodes.append(t_prime)
                    capacities.append(int(a_exc))
                    unit_costs.append(0)
                    # print("Adding arc ({}, {}) with cost 0 and cap {}".
                    #       format(v, t_prime, int(a_exc)))
                    # update A
                    A += a_exc
        # process x node
        a_exc = out_weight_x - in_weight_x
        if a_exc < 0:
            # add edge (s', x)
            start_nodes.append(s_prime)
            end_nodes.append(x)
            capacities.append(int(-a_exc))
            unit_costs.append(0)
            # print("Adding arc ({}, {}) with cost 0 and cap {}".format(
            #    s_prime,
            #    x,
            #    int(-a_exc)))
        if a_exc > 0:
            # add edge (x, t')
            start_nodes.append(x)
            end_nodes.append(t_prime)
            capacities.append(int(a_exc))
            unit_costs.append(0)
            # print("Adding arc ({}, {}) with cost 0 and cap {}".format(
            #    x,
            #    t_prime,
            #    int(a_exc)))
            # update A
            A += a_exc
        # we must send flow of A from s_prime to t_prime
        supplies = [0]*(len(self) + 3)
        supplies[s_prime] = int(A)
        supplies[t_prime] = int(-A)
        # Instantiate a SimpleMinCostFlow solver.
        min_cost_flow = pywrapgraph.SimpleMinCostFlow()
        # Add each arc.
        for i in range(len(start_nodes)):
            min_cost_flow.AddArcWithCapacityAndUnitCost(start_nodes[i],
                                                        end_nodes[i],
                                                        capacities[i],
                                                        unit_costs[i])
        # Add node supplies
        for i in range(0, len(supplies)):
            min_cost_flow.SetNodeSupply(i, supplies[i])
        # Find the minimum cost flow between node s' and t'.
        if min_cost_flow.Solve() == min_cost_flow.OPTIMAL:
            # print('Minimum cost:', min_cost_flow.OptimalCost())
            # print('')
            # print(' Arc     Flow / Capacity Cost')
            for i in range(min_cost_flow.NumArcs()):
                # cost = min_cost_flow.Flow(i)*min_cost_flow.UnitCost(i)
                # print('%1s -> %1s   %3s / %3s   %3s' % (
                #    min_cost_flow.Tail(i),
                #    min_cost_flow.Head(i),
                #    min_cost_flow.Flow(i),
                #    min_cost_flow.Capacity(i),
                #    cost))
                # update arcs
                start = min_cost_flow.Tail(i)
                destin = min_cost_flow.Head(i)
                if start != s_prime and \
                        start != t_prime and \
                        start != x and \
                        destin != s_prime and \
                        destin != t_prime and \
                        destin != x:
                    # if forward, increase flow. otherwise decrease.
                    # print("Processing edge ({}, {})".format(start, destin))
                    if start < destin:
                        sup_flow = min_cost_flow.Flow(i)
                    else:
                        sup_flow = -min_cost_flow.Flow(i)
                        temp_start = start
                        start = destin
                        destin = temp_start
                    # print("Has become ({}, {}) with sup {}".format(start,
                    #                                               destin,
                    #                                               sup_flow))
                    arc = self.get_arc(start, destin)
                    if (sup_flow != 0) or ("lower_bound" not in
                                           self.arc_info[arc].keys()):
                        # print("We should add this")
                        old_flow = self.arc_info[arc]["weight"]
                        bound_1 = old_flow + sup_flow
                        bound_2 = old_flow - sup_flow
                        new_lb = max(0, int(min(bound_1, bound_2)))
                        new_ub = int(max(bound_1, bound_2))
                        if wide:
                            if new_lb == new_ub:
                                # print("We had a zero interval")
                                new_lb = int(new_lb*0.8)
                                new_ub = int(new_ub*1.2)
                                if new_lb == 0:
                                    # print("We got a zero lower bound")
                                    new_ub = 5
                                # print("But now we're doing {} {}".
                                #       format(new_lb, new_ub))

                        self.arc_info[arc]["lower_bound"] = new_lb
                        self.arc_info[arc]["upper_bound"] = new_ub
                        # print("Edge ({},{}) bounds are [{},{}]".format(
                        #    start,
                        #    destin,
                        #    self.arc_info[arc]["lower_bound"],
                        #    self.arc_info[arc]["upper_bound"]))
                    # print(self.arc_info[arc])
        else:
            print('There was an issue with the min cost flow input.')
        # self.check_conservation_of_flow() # check that solution is valid

    def get_weight_from_minflow(self):
        """Use the minflow approach from Traph to find a flow."""
        start_nodes = []
        end_nodes = []
        capacities = []
        unit_costs = []
        A = 0
        s_prime = self.sink() + 1
        t_prime = self.sink() + 2
        x = self.sink() + 3
        # for every edge in the graph, add edge to mincost flow instance with
        # infinite capacity and cost 1
        # also add backwards edge
        for arc in self.arc_info.keys():
            # forward edge
            start_nodes.append(self.arc_info[arc]["start"])
            end_nodes.append(self.arc_info[arc]["destin"])
            capacities.append(100000)  # capacity of 100,000 instead of inf
            unit_costs.append(1)
            print("Adding arc ({}, {}) with unit cost and cap inf".format(
                self.arc_info[arc]["start"],
                self.arc_info[arc]["destin"]))
            # backward edge
            start_nodes.append(self.arc_info[arc]["destin"])
            end_nodes.append(self.arc_info[arc]["start"])
            capacities.append(int(self.arc_info[arc]["weight"]))  # no negative
            unit_costs.append(1)
            print("Adding arc ({}, {}) with unit cost and cap inf".format(
                self.arc_info[arc]["destin"],
                self.arc_info[arc]["start"]))
        # add (x,s) and (t,x) edges with same cap, cost as above
        in_weight_x = 0
        for in_arc in self.in_arcs_lists[self.sink()]:
            in_weight_x += self.arc_info[in_arc]["weight"]
        out_weight_x = 0
        for out_arc in self.out_arcs_lists[self.source()]:
            out_weight_x += self.arc_info[out_arc]["weight"]
        # (x,s)
        start_nodes.append(x)
        end_nodes.append(self.source())
        capacities.append(100000) # capacity of 100,000 instead of inf
        unit_costs.append(1)
        print("Adding arc ({}, {}) with unit cost and cap inf".format(
            x,
            self.source()))
        # backward
        start_nodes.append(self.source())
        end_nodes.append(x)
        capacities.append(int(out_weight_x)) # don't go negative
        unit_costs.append(1)
        print("Adding arc ({}, {}) with unit cost and cap inf".format(
            self.source(),
            x))
        # (t,x)
        start_nodes.append(self.sink())
        end_nodes.append(x)
        capacities.append(100000) # capacity of 100,000 instead of inf
        unit_costs.append(1)
        print("Adding arc ({}, {}) with unit cost and cap inf".format(
            self.sink(),
            x))
        # backward
        start_nodes.append(x)
        end_nodes.append(self.sink())
        capacities.append(int(in_weight_x)) # don't go negative
        unit_costs.append(1)
        print("Adding arc ({}, {}) with unit cost and cap inf".format(
            x,
            self.sink()))
        # for all verts, if a-exc < 0, add edge (s', v) with capacity -a-exc(v)
        # and cost 0, and if a-exc > 0, add edge (v, t') with capacity a-exc(v)
        # and cost 0.
        for v in self:
            # process internal verts only, since we assume source and sink have
            # no in and out edges respectively
            if v != self.source() and v != self.sink():
                # compute a-exc(v)
                in_weight = 0
                for in_arc in self.in_arcs_lists[v]:
                    in_weight += self.arc_info[in_arc]["weight"]
                out_weight = 0
                for out_arc in self.out_arcs_lists[v]:
                    out_weight += self.arc_info[out_arc]["weight"]
                a_exc = out_weight - in_weight
                if a_exc < 0:
                    # add edge (s', v)
                    start_nodes.append(s_prime)
                    end_nodes.append(v)
                    capacities.append(int(-a_exc))
                    unit_costs.append(0)
                    print("Adding arc ({}, {}) with cost 0 and cap {}".format(
                        s_prime,
                        v,
                        int(-a_exc)))
                if a_exc > 0:
                    # add edge (v, t')
                    start_nodes.append(v)
                    end_nodes.append(t_prime)
                    capacities.append(int(a_exc))
                    unit_costs.append(0)
                    print("Adding arc ({}, {}) with cost 0 and cap {}".format(
                        v,
                        t_prime,
                        int(a_exc)))
                    # update A
                    A += a_exc
        # process x node
        a_exc = out_weight_x - in_weight_x
        if a_exc < 0:
            # add edge (s', x)
            start_nodes.append(s_prime)
            end_nodes.append(x)
            capacities.append(int(-a_exc))
            unit_costs.append(0)
            print("Adding arc ({}, {}) with cost 0 and cap {}".format(
                s_prime,
                x,
                int(-a_exc)))
        if a_exc > 0:
            # add edge (x, t')
            start_nodes.append(x)
            end_nodes.append(t_prime)
            capacities.append(int(a_exc))
            unit_costs.append(0)
            print("Adding arc ({}, {}) with cost 0 and cap {}".format(
                x,
                t_prime,
                int(a_exc)))
            # update A
            A += a_exc
        # we must send flow of A from s_prime to t_prime
        supplies = [0]*(len(self) + 3)
        supplies[s_prime] = int(A)
        supplies[t_prime] = int(-A)
        # Instantiate a SimpleMinCostFlow solver.
        min_cost_flow = pywrapgraph.SimpleMinCostFlow()
        # Add each arc.
        for i in range(len(start_nodes)):
            min_cost_flow.AddArcWithCapacityAndUnitCost(start_nodes[i],
            end_nodes[i], capacities[i], unit_costs[i])
        # Add node supplies
        for i in range(0, len(supplies)):
            min_cost_flow.SetNodeSupply(i, supplies[i])
        # Find the minimum cost flow between node s' and t'.
        if min_cost_flow.Solve() == min_cost_flow.OPTIMAL:
            print('Minimum cost:', min_cost_flow.OptimalCost())
            print('')
            print(' Arc     Flow / Capacity Cost')
            for i in range(min_cost_flow.NumArcs()):
                cost = min_cost_flow.Flow(i)*min_cost_flow.UnitCost(i)
                print('%1s -> %1s   %3s / %3s   %3s' % (
                    min_cost_flow.Tail(i),
                    min_cost_flow.Head(i),
                    min_cost_flow.Flow(i),
                    min_cost_flow.Capacity(i),
                    cost))
                # update arcs
                start = min_cost_flow.Tail(i)
                destin = min_cost_flow.Head(i)
                if start != s_prime and \
                        start != t_prime and \
                        start != x and \
                        destin != s_prime and \
                        destin != t_prime and \
                        destin != x:
                    # if forward, increase flow. otherwise decrease.
                    print("Processing edge ({}, {})".format(start, destin))
                    if start < destin:
                        sup_flow = min_cost_flow.Flow(i)
                    else:
                        sup_flow = -min_cost_flow.Flow(i)
                        temp_start = start
                        start = destin
                        destin = temp_start
                    print("Has become ({}, {}) with sup {}".format(start,
                                                                   destin,
                                                                   sup_flow))
                    arc = self.get_arc(start, destin)
                    if (sup_flow != 0) or ("lower_bound" not in \
                            self.arc_info[arc].keys()):
                        print("We should add this")
                        old_flow = self.arc_info[arc]["weight"]
                        new_flow = old_flow + sup_flow
                        self.arc_info[arc]["weight"] = int(new_flow)
                        print("Edge ({},{}) weight is changed from {} to {}".format(
                            start,
                            destin,
                            old_flow,
                            new_flow))
        else:
            print('There was an issue with the min cost flow input.')
        #self.check_conservation_of_flow() # check that solution is valid


    def get_interval_from_confidence_file(self, interval_dict):
        """Create upper and lower bounds from interval dict created from
        confidence file."""
        for arc in self.arc_info.keys():
            weight = self.arc_info[arc]["weight"]
            if weight == 0:
                interval = [0, 0]
            else:
                interval = interval_dict[weight]
            ub = interval[1]
            lb = interval[0]
            self.arc_info[arc]["upper_bound"] = ub
            self.arc_info[arc]["lower_bound"] = lb


    def create_simple_intervals(self, factor):
        """Create intervals of (1-factor)*measured, (1+factor)*measured"""
        for arc in self.arc_info.keys():
            weight = self.arc_info[arc]["weight"]
            lb = int(np.around(weight*(1-factor)))
            ub = int(np.around(weight*(1+factor)))
            self.arc_info[arc]["upper_bound"] = ub
            self.arc_info[arc]["lower_bound"] = lb

    def perturb_edges(self, epsilon, seed):
        np.random.seed(seed)
        for arc in self.arc_info.keys():
            original_flow = self.arc_info[arc]["weight"]
            sd = original_flow*epsilon
            new_flow = np.around(np.random.normal(original_flow, sd))
            self.arc_info[arc]["weight"] = new_flow
            #print("Arc {} ({},{}) perturbed from {} to {}".format(
            #    arc,
            #    self.arc_info[arc]["start"],
            #    self.arc_info[arc]["destin"],
            #    original_flow,
            #    new_flow))

    def update_flow(self):
        """Use ortools to solve maxflow problem to try to find a feasible
        flow"""
        start_nodes = []
        end_nodes = []
        capacities = []
        # (1): add all edges (u, v) with capacity ub-lb
        B = self.get_max_lb()*(self.num_edges() - len(self) + 2)
        for arc in self.arc_info.keys():
            if self.arc_info[arc]["upper_bound"] == float('inf'):
                self.arc_info[arc]["upper_bound"] = B
        for arc in self.arc_info.keys():
            start_nodes.append(self.arc_info[arc]["start"])
            end_nodes.append(self.arc_info[arc]["destin"])
            capacities.append(int(self.arc_info[arc]["upper_bound"]\
                    - self.arc_info[arc]["lower_bound"]))
        # (2): add edge (t, s) with capacity B
        # B = max_lb * (m - n + 2)
        B = self.get_max_lb()*(self.num_edges() - len(self) + 2)
        if B == 0:
            #B = float('inf')
            B = 100000
        start_nodes.append(self.sink())
        end_nodes.append(self.source())
        capacities.append(int(B))
        # (3): for all verts, if exc > 0, add edge (s', v) with capacity exc(v),
        # and if exc < 0, add edge(s', v) with capacity -exc(v)
        s_prime = max(self.vertices) + 1
        t_prime = max(self.vertices) + 2
        print("s'={}, t'={}".format(s_prime, t_prime))
        for v in self:
            #print("vert {} in arcs: {}".format(v,
            #    self.in_arcs_lists[v]))
            # compute exc: lower bounds of in - lower bounds of out
            sum_lb_in = 0
            for in_arc in self.in_arcs_lists[v]:
                sum_lb_in += self.arc_info[in_arc]["lower_bound"]
            sum_lb_out = 0
            #print("vert {} out arcs: {}".format(v,
            #    self.out_arcs_lists[v]))
            for out_arc in self.out_arcs_lists[v]:
                sum_lb_out += self.arc_info[out_arc]["lower_bound"]
            exc = sum_lb_in - sum_lb_out
            #print("exc is {}".format(exc))
            if exc > 0:
                start_nodes.append(s_prime)
                end_nodes.append(v)
                capacities.append(int(exc))
            else:
                start_nodes.append(v)
                end_nodes.append(t_prime)
                capacities.append(int(-exc))
        # solve maxflow
        #print("s' is {} and t' is {}".format(s_prime, t_prime))
        max_flow = pywrapgraph.SimpleMaxFlow()
        for u, v, cap in zip(start_nodes, end_nodes, capacities):
            #print("Adding edge {}, {} with cap {}".format(u,v,cap))
            max_flow.AddArcWithCapacity(u, v, cap)
        success = True
        if max_flow.Solve(s_prime, t_prime) == max_flow.OPTIMAL:
            #print('Max flow: {}'.format( max_flow.OptimalFlow()))
            #print('  Arc    Flow / Capacity')
            for i in range(max_flow.NumArcs()):
               # print('%1s -> %1s   %3s  /  %3s' % (
               #         max_flow.Tail(i),
               #         max_flow.Head(i),
               #         max_flow.Flow(i),
               #         max_flow.Capacity(i)))
                # check that (s', v) edges are saturated (once we find a false,
                # stay false forever)
                if success:
                    if max_flow.Tail(i) == s_prime:
                        success = max_flow.Flow(i) == max_flow.Capacity(i)
        else:
            success = False
            print('There was an issue with the max flow input.')
        if success:
            # update the flows to be the flow found from maxflow problem
            for i in range(max_flow.NumArcs()):
                # if this is an original arc, update the flow
                if max_flow.Tail(i) != s_prime \
                    and max_flow.Head(i) != t_prime \
                    and not (max_flow.Tail(i) == self.sink() \
                    and max_flow.Head(i) == self.source()):
                        # update arc
                        start = max_flow.Tail(i)
                        destin = max_flow.Head(i)
                        arc = self.get_arc(start, destin)
                        new_flow = self.arc_info[arc]["lower_bound"] + max_flow.Flow(i)
                        old_flow = self.arc_info[arc]["weight"]
                        self.arc_info[arc]["weight"] = new_flow
                        #print("Edge {} {} adjusted from {} to {}".format(
                        #    start,
                        #    destin,
                        #    old_flow,
                        #    new_flow
                        #    ))
            self.check_conservation_of_flow() # check that solution is valid
            return True
        else:
            return False


    def get_max_lb(self):
        """Return the maximum lower bound across all edges."""
        max_lb = 0
        for arc in self.arc_info.keys():
            if self.arc_info[arc]["lower_bound"] > max_lb:
                    max_lb = self.arc_info[arc]["lower_bound"]
        return max_lb


    def path_splice(self, timeout = 60):
        """Execute path splicing."""

        def compute_bounds(edges, triple):
            #print("Examining edges {}".format(edges))
            lower_bounds = [0]
            # if no edges, we'll return a big number as the upper bound.
            upper_bounds = [float("inf")]
            for arc in edges:
                l_e = self.arc_info[arc]["lower_bound"]
                u_e = self.arc_info[arc]["upper_bound"]
                #print("For arc {}, l_e = {} and u_e = {}".format(arc, l_e, u_e))
                f_mijk = compute_f_mijk(arc, triple)
                #print("f_mijk = {}".format(f_mijk))
                lower_bounds.append(l_e - f_mijk)
                upper_bounds.append(u_e - f_mijk)
            #print("lower bounds: {}".format(lower_bounds))
            #print("upper bounds: {}".format(upper_bounds))
            lb = max(lower_bounds)
            # in case no edges in here, make max of 5,000
            print("There are no arcs in edges (triple)")
            ub = min(upper_bounds + [5000])
            return(lb, ub)


        def get_nodes(path):
            node_seq = [self.source()]
            for arc in path:
                node_seq.append(self.arc_info[arc]['destin'])
            return(node_seq)

        def compute_fwd(p1, p2):
            """Find the largest index on which the vertices of p1 and p2
            are the same."""
            for k in range(len(p2)):
                if p1[k] != p2[k]:
                    break
            return(k)


        def compute_rev(p1, p2):
            """Find the largest index on which the vertices of p1 and p2
            are the same, from t rather than s."""
            p1 = list(reversed(p1))
            p2 = list(reversed(p2))
            return(compute_fwd(p1, p2))


        def compute_f_mijk(arc_id, triple):
            """
            For the given edge, compute the flow on that edge
            contributed by paths other than p1, p2, and p3.
            """
            f_e = self.arc_info[arc_id]["weight"]
            #print("flow on edge is {}".format(f_e))
            paths = [self.paths[triple[x]] for x in [0,1,2]]
            #print("Computing f_mijk for arc {}".format(arc_id))
            indices = [i for i,path in enumerate(paths) if arc_id in path]
            p_e = [self.paths.index(path) for path in paths if arc_id in path]
            #print("paths of indices {}: {}".format(triple, paths))
            #print("indices of paths i,j,k on this edge: {}".format(p_e))
            weights = [self.weights[i] for i in p_e]
            #print("weights: {}".format(weights))
            return(f_e - sum(weights))

        # https://www.geeksforgeeks.org/perpendicular-distance-between-a-point-and-a-line-in-2-d/
        def distance_point_to_line(x1, y1, a, b, c):
            """
            Given a point (p1, p2), find shortest distance to
            line ax+by+c=0.
            """
            d = abs((a * x1 + b * y1 + c)) / (math.sqrt(a * a + b * b))
            #print("Distance from ({}, {}) to line {}x+{}y+{}=0 is {}".format(
            #        x1, y1, a, b, c, d))
            return(d)


        def center_flows(L_wprime, U_wprime, L_w3, U_w3, L_overlap, U_overlap):
            """
            For the set of bounds, find flow for w_prime and w_3
            that maximize distance to the bounds.
            """
            # examine every possible point
            current_dist_to_edge = -1
            point = (0,0)
            #print("w3 range: [{}, {}]".format(L_w3, U_w3))
            #print("w' range: [{}, {}]".format(L_wprime, U_wprime))
            #print("overlap range: [{},{}]".format(L_overlap, U_overlap))
            for y in range(L_w3, U_w3 + 1):
                #print("y={}".format(y))
                LH_bound = max(L_wprime, L_overlap - y)
                #print("LH bound = {}".format(LH_bound))
                RH_bound = min(U_wprime, U_overlap - y)
                #print("RH bound = {}".format(RH_bound))
                for x in range(LH_bound, RH_bound + 1):
                    # w3 UB: 0x + 1y - U_w3 = 0
                    # w3 LB: 0x + 1y - L_w3 = 0
                    # wprime UB: 1x + 0y - U_wprime
                    # wprime LB: 1x + 0y - L_wprime
                    # wprime + w3 UB: 1x + 1y - U_wprime,wk
                    # wprime + w3 LB: 1x + 1y - L_wprime,wk
                    dist_to_edge = min(distance_point_to_line(x, y, 0, -1, U_w3), #0x-1y+U_w3=0
                                       distance_point_to_line(x, y, 0, -1, L_w3), #0x-1y+L_w3=0
                                       # -1x + 0y + U_wprime = 0
                                       distance_point_to_line(x, y, -1, 0, U_wprime),
                                       # -1x + 0y + L_wprime = 0
                                       distance_point_to_line(x, y, -1, 0, L_wprime),
                                       # -1x - 1y + U_overlap = 0
                                       distance_point_to_line(x, y, -1, -1, U_overlap),
                                       # -1 x - y + L_overlap = 0
                                       distance_point_to_line(x, y, -1, -1, L_overlap))
                    if dist_to_edge > current_dist_to_edge:
                        #print("At point ({},{}), distance to edge increased from {} to {}."\
                        #        .format(x,y,current_dist_to_edge,dist_to_edge))
                        current_dist_to_edge = dist_to_edge
                        point = (x,y)
            return(point)

        def attempt_splice(triple):
            """Check that the triple can be spliced.
            Conditions:
            (1) len(pk) - rev(k, j) + 1 leq fwd(i, k)
            (2) there is a compatible flow
            """

            def overlap_condition(triple):
                """
                Decide whether these paths meet the overlap condition.
                Return fwd, rev, and overlap for next steps.
                """
                p3_len = len(self.paths[triple[2]])

                fwd = compute_fwd(self.paths[triple[0]], self.paths[triple[2]])
                rev = compute_rev(self.paths[triple[2]], self.paths[triple[1]])
                overlap = rev + fwd - p3_len
                if fwd + rev - p3_len >= 0:
                    print("#    Triple {} meets overlap condition.".format(triple))
                    #print("fwd = {}, rev = {}, lap = {}".format(fwd, rev, overlap))
                    return(True, fwd, rev, overlap)
                return(False, fwd, rev, overlap)


            def flow_condition(p_prime, p3, triple):
                """Process two potential paths resulting from a set of three
                paths."""

                all_edges = set(self.arc_info.keys())
                not_p_prime = all_edges.difference(set(p_prime))
                #print("Not p_prime: {}".format(not_p_prime))
                not_p3 = all_edges.difference(set(p3))
                #print("Not p_3: {}".format(not_p3))
                p_prime_alone = list(set(p_prime).intersection(not_p3))
                #print("p_prime_alone: {}".format(p_prime_alone))
                p3_alone = list(set(p3).intersection(not_p_prime))
                #print("p3 alone: {}".format(p3_alone))
                overlap = list(set(p3).intersection(p_prime))
                #print("overlap alone: {}".format(overlap))

                #print("computing L_wprime and U_wprime")
                L_wprime, U_wprime = compute_bounds(p_prime_alone, triple)
                #print("computing L_w3 and U_w3")
                L_w3, U_w3 = compute_bounds(p3_alone, triple)
                #print("computing L_overlap and U_overlap")
                L_overlap, U_overlap = compute_bounds(overlap, triple)
                #print("L_wprime, U_wprime: {} {}".format(L_wprime, U_wprime))
                #print("L_w3, U_w3: {} {}".format(L_w3, U_w3))
                #print("{} <= {}".format(L_overlap, U_wprime + U_w3))
                #print("{} >= {}".format(U_overlap, L_wprime + L_w3))
                meets_conditions = (L_wprime <= U_wprime) & \
                                    (L_w3 <= U_w3) & \
                                    (L_overlap <= U_wprime + U_w3) & \
                                    (L_wprime + L_w3 <= U_overlap)
                if meets_conditions:
                    w_prime, w3 = center_flows(L_wprime, U_wprime,
                                        L_w3, U_w3,
                                        L_overlap, U_overlap)
                    # change paths
                    # first, delete:
                    for index in sorted(triple, reverse=True):
                        del self.paths[index]
                        del self.weights[index]
                    # now, add:
                    self.paths.append(p3)
                    self.paths.append(p_prime)
                    self.weights.append(w3)
                    self.weights.append(w_prime)
                    # update weights on edges
                    self.update_edge_weights()
                    self.check_flow()
                    self.check_paths()
                    return(True)
                else:
                    return(False)


            def check_flow_conditions(triple, fwd, rev, overlap):
                """Check that the flow condition is met.
                If it is, return the new paths with weights."""

                p1, p2, p3 = [self.paths[triple[x]] for x in [0,1,2]]
                p2_end_index = len(p2) - rev + overlap
                #print("p2_end_index = {}".format(p2_end_index))
                p1_start_index = fwd + 1
                #print("p1_start_index = {}".format(p1_start_index))
                #print("p1 subset: {}".format(p1[p1_start_index - 1:]))
                #print("p2 subset = {}".format(p2[:p2_end_index]))
                p_prime = p2[:p2_end_index] + p1[p1_start_index - 1:]
                #print("p_prime = {}".format(p_prime))

                # try to rebalance
                if flow_condition(p1, p2, triple):
                    print("Rebalance opportunity found. Now rebalancing.")
                    self.rebalances += 1
                    return(True)

                # try to splice and merge
                if flow_condition(p_prime, p3, triple):
                    print("Splice+merge opportunity found. Now splicing.")
                    self.splices += 1
                    return(True)

                return(False)


            #print("#  Can we splice {}?".format(
            #                          [self.paths[x] for x in triple]))
            overlap_true, fwd_index, rev_index, overlap = overlap_condition(
                                                            triple)
            if overlap_true:
                self.overlap_count += 1
                return(check_flow_conditions(triple,
                                fwd_index, rev_index, overlap))
            return(False)


        overall_start_time = time.time()
        # while there is an unchecked triple of paths p_i, p_j, p_k:
        perm_start_time = time.time()
        print("Num paths: {}".format(len(self.paths)))
        triples = set(permutations(range(len(self.paths)),3))
        print("Number triples: {}".format(len(triples)))
        print("Time to calculate triples: {}".format(
            time.time() - perm_start_time))
        checked_triples = set()
        iteration_count = 0
        while triples:
            iteration_count += 1
            triple = triples.pop()
            checked_triples.add(triple)
            if attempt_splice(triple):
                all_triples = set(permutations(range(len(self.paths)),3))
                triples = all_triples.difference(checked_triples)
            if timeout is not None:
                if time.time() - overall_start_time > timeout:
                    print("Iteration count: {}".format(iteration_count))
                    break

        print("Iteration count: {}".format(iteration_count))

    def get_overlapping_path_pairs(self):
        """Return all pairs of paths that overlap by index in self.paths."""
        path_pairs = []
        for i, path_1 in enumerate(self.paths):
            for j, path_2 in enumerate(self.paths):
                if j != i:
                    if len(set(path_1).intersection(set(path_2))) != 0:
                        path_pairs.append((i,j))
        path_pairs.sort()
        return path_pairs


    def compute_pair_bounds(self, edges, pair):
        """
        Compute the restricting lower and upper bounds for the set of edges,
        without the weights from the pair of paths.
        Edges is the set of edges to be considered (i.e., pi alone, pj alone,
        or overlap between pi and pj). Pair is (i, j).
        """
        lower_bounds =[]
        upper_bounds = []
        for arc in edges:
            l_e = self.arc_info[arc]["lower_bound"]
            u_e = self.arc_info[arc]["upper_bound"]
            f_mij = self.compute_f_mij(arc, pair)
            lower_bounds.append(l_e - f_mij)
            upper_bounds.append(u_e - f_mij)
        lb = max(lower_bounds + [0])
        # in case no edges in here, make max of 5,000
        if len(upper_bounds) == 0:
            i = pair[0]
            j = pair[1]
            print("Path i ({}): {}".format(i, self.paths[i]))
            print("Path j ({}): {}".format(j, self.paths[j]))
        ub = min(upper_bounds + [5000])
        #print("lower bounds: {}".format(lower_bounds))
        #print("upper bounds: {}".format(upper_bounds))
        return(lb, ub)

    def compute_f_mij(self, arc_id, pair):
        """
        For the given edge, compute the flow on that edge
        contributed by paths other than pi and pj.
        """
        f_e = self.arc_info[arc_id]["weight"]
        w_i = self.weights[pair[0]]
        w_j = self.weights[pair[1]]
        p_i = self.paths[pair[0]]
        p_j = self.paths[pair[1]]
        to_subtract = 0
        if arc_id in p_i:
            to_subtract += w_i
        if arc_id in p_j:
            to_subtract += w_j
        return f_e - to_subtract


    def find_wj(self, L_wi, U_wi, L_wj, U_wj, L_overlap, U_overlap):
        """
        Given bounds, determine either that no w_j can exist, or find it.
        """
        # these conditions determine whether there is any solution
        exists_feasible_region = (L_wi <= U_wi) and \
                            (L_wj <= U_wj) and \
                            (L_overlap <= U_wi + U_wj) and \
                            (L_wi + L_wj <= U_overlap)

        zero_in_feasible_region = (L_wi <= 0) and \
                                (U_wi >= 0) and \
                                (L_overlap <= U_wj) and \
                                (U_overlap >= L_wj)

        if exists_feasible_region and zero_in_feasible_region:
            # return the flow in the center
            bottom = max(L_overlap, L_wj)
            top = min(U_overlap, U_wj)
            print(bottom, top)
            return int((bottom + top)/2)
        else:
            return None


    def pairwise_rebalance(self):
        """Execute pairwise rebalancing (heuristic c)"""
        path_pairs = self.get_overlapping_path_pairs()
        if len(path_pairs) > 0:
            pair = path_pairs.pop()
        else:
            pair = None
        while pair is not None:
            i = pair[0]
            j = pair[1]
            print("Testing {},{}".format(i, j))
            print("weight i: {}, weight j: {}".format(self.weights[i],
            self.weights[j]))
            p_i = self.paths[i]
            p_j = self.paths[j]
            p_i_alone = set(p_i).difference(set(p_j))
            p_j_alone = set(p_j).difference(set(p_i))
            overlap = set(p_i).intersection(set(p_j))
            print("Finding bounds for i")
            L_wi, U_wi = self.compute_pair_bounds(p_i_alone, pair)
            print("Finding bounds for j")
            L_wj, U_wj = self.compute_pair_bounds(p_j_alone, pair)
            print("Finding bounds for overlap")
            L_overlap, U_overlap = self.compute_pair_bounds(overlap, pair)
            w_j = self.find_wj(L_wi, U_wi, L_wj, U_wj, L_overlap, U_overlap)
            if w_j is not None:
                # rebalance is possible
                # set weight of j to w_j
                print("Removing path {}".format(i))
                print("W_j was {}".format(w_j))
                print("Path i w={}  is {}".format(self.weights[i], p_i))
                print("path j w={} is {}".format(self.weights[j], p_j))
                print(("L_wi={}, U_wi={}, L_wj={}, U_wj={}, L_overlap={}," +\
                            "U_overlap={}").format(L_wi, U_wi, L_wj, U_wj,
                            L_overlap, U_overlap))
                self.weights[j] = w_j
                # remove path i and weight j
                del self.paths[i]
                del self.weights[i]
                # udpate the edge weights based on new paths
                self.update_edge_weights()
                # increment counter
                self.pairwise_rebalances += 1
                # recompute overlapping pairs.
                # TODO: do this more efficiently.
                path_pairs = self.get_overlapping_path_pairs()

                print("Checking bounds")
                self.check_flow()
            # update current pair
            if path_pairs:
                pair = path_pairs.pop()
            else:
                pair = None


    def get_path_nodes(self, path):
        """Given a list of arc ids, return an ordered list of unique nodes in the path.
        """
        nodes = []
        for arc in path:
            start = self.arc_info[arc]["start"]
            destin = self.arc_info[arc]["destin"]
            nodes.append(start)
            nodes.append(destin)
        nodes = list(set(nodes))
        nodes.sort()
        return nodes


    def get_potential_pw_splice_pairs(self):
        """Find all pairs of paths that share a node."""
        self.print_out()
        path_pairs = []
        for i, path_1 in enumerate(self.paths):
            for j, path_2 in enumerate(self.paths):
                if j != i:
                    p1_nodes = self.get_path_nodes(path_1)[1:-1]
                    p2_nodes = self.get_path_nodes(path_2)[1:-1]
                    if len(set(p1_nodes).intersection(set(p2_nodes))) != 0:
                        path_pairs.append((i,j))
        path_pairs.sort()
        return path_pairs


    def get_spliced_paths(self, p_i, p_j):
        """Given paths p_i and p_j passing through a common node, return the two
        paths resulting from splicing p_i and p_j."""
        p_i_nodes = self.get_path_nodes(p_i)[1:-1]
        p_j_nodes = self.get_path_nodes(p_j)[1:-1]
        # we will splice at least common node
        print("Path we are attempting to splice")
        print(p_i, p_j)
        print(p_i_nodes, p_j_nodes)
        if len(set(p_i_nodes).intersection(set(p_j_nodes))) == 0:
            print("no overlap")
        common_node = min(set(p_i_nodes).intersection(set(p_j_nodes)))
        # find where p_i gets to this node
        index_i = 0
        index_j = 0
        for index, arc in enumerate(p_i):
            destin = self.arc_info[arc]["destin"]
            if destin == common_node:
                index_i = index + 1
                break
        for index, arc in enumerate(p_j):
            destin = self.arc_info[arc]["destin"]
            if destin == common_node:
                index_j = index + 1
                break
        p_i_prime = p_j[:index_j] + p_i[index_i:]
        p_j_prime = p_i[:index_i] + p_j[index_j:]
        return (p_i_prime, p_j_prime)



    def pairwise_splice(self):
        """Execute pairwise splice."""
        # If two paths share a node, consider splicing them.
        path_pairs = self.get_potential_pw_splice_pairs()
        print("Weights: {}".format(self.weights))
        print("Path pairs for splicing is: {}".format(path_pairs))
        if len(path_pairs) > 0:
            pair = path_pairs.pop()
        else:
            pair = None
        while pair is not None:
            i = pair[0]
            j = pair[1]
            p_i = self.paths[i]
            p_j = self.paths[j]
            p_i, p_j = self.get_spliced_paths(p_i, p_j)
            p_i_alone = set(p_i).difference(set(p_j))
            p_j_alone = set(p_j).difference(set(p_i))
            overlap = set(p_i).intersection(set(p_j))
            print("Examining pair ({},{})".format(i,j))
            L_wi, U_wi = self.compute_pair_bounds(p_i_alone, pair)
            L_wj, U_wj = self.compute_pair_bounds(p_j_alone, pair)
            L_overlap, U_overlap = self.compute_pair_bounds(overlap, pair)
            w_j = self.find_wj(L_wi, U_wi, L_wj, U_wj, L_overlap, U_overlap)
            if w_j is not None:
                print("This pair can be spliced.")
                # splice is possible
                # replace jth path with p_j with weight w_j
                # check whether p_j is in paths already. if yes, just increment
                # weight.
                if p_j in self.paths:
                    print("P_j is in paths")
                self.paths[j] = p_j
                self.weights[j] = w_j
                # remove path i and weight j
                del self.paths[i]
                del self.weights[i]
                # udpate the edge weights based on new paths
                self.update_edge_weights()
                # increment counter
                self.pairwise_splices += 1
                # recompute overlapping pairs.
                # TODO: do this more efficiently.
                path_pairs = self.get_potential_pw_splice_pairs()
                self.check_flow()
            # update current pair
            if path_pairs:
                pair = path_pairs.pop()
            else:
                pair = None


