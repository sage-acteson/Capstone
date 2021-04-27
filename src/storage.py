""" This file will hold classes that store information
that is passed between other classes. This includes
StoredReads and certain graph data.

author: Sage Acteson
"""

class StoredReads:
    """This only stores read in information. It helps
    the code mesh with the UML diagrams
    """
    def __init__(self, reads=[]):
        self.stored_reads = reads

    def set_reads(self, reads):
        self.storedReads = reads

    def get_reads(self):
        return self.stored_reads


class FlowGraph:
    """This contains the information and functionality
    for a high-level Flow Graph. Edges in this have an associated flow
    """
    def __init__(self, num_nodes):
        self.num_nodes = num_nodes
        self.nodes = list(range(num_nodes)) # keep track of unique nodes used
        self.new_source = None # the id of the new source node, s', that is added

        # Constrained Flow Graph (edges and flow for a flow graph with subpaths)
        # Assumes that there are no edges leaving the sink node, the sink node
        # is the last node, and the nodes are sequential and start at 0
        # In the form {u : {v1 : f1, v2 : f2, ...}, ...}
        self.cfg = {new_dict : dict() for new_dict in range(num_nodes-1)}

        # Subpaths for the CFG (Constrained Flow Graph)
        # In the format [{"edges":[(),()..],"demand":X,"constraint_edge_nodes":(xi,yi)},...]
        self.subpaths = [] 

        # Inexact Flow Graph (flow graph with intervals for where subpaths have been applied)
        # In the form { 'u_v' : (lb, ub)}
        self.ifg = dict() 

        # Stores the mapping for subpaths so they can be converted to the original nodes later.
        # In the form { "x_y" : [nodes between w and z]} 
        # with longer subpaths this would map to more than just u,v
        self.subpath_map = dict()

    def add_edge(self, u ,v, flow):
        """ Take in two vertices and the flow between them and add
        it to the graph.
        """
        self.cfg[u][v] = flow

    def add_subpath(self, subpath):
        """ Take in a subpath as a string and add it to the graph

        This takes in the subpath as a string of space-separated values.
        The last value is a float representing the demand of the 
        subpath and the other values are ints representing the nodes in
        the path. 
        """
        new_subpath = dict()
        info = subpath.split()
        new_subpath["demand"] = float(info[-1])
        # Add edges.
        edges = []
        for x in range(len(info)-2):
            edges.append((int(info[x]),int(info[x+1])))
        new_subpath["edges"] = edges
        self.subpaths.append(new_subpath)

    def apply_constraints(self):
        """ Generate IFG (Inexact Flow Graph) based on 
        constraints outlined in subpaths. The solution to this IFG 
        can be found using the core IFD program.
        """
        # 1. Add subpath constraint edges with Ie = [0,f(e)]
        for subpath in self.subpaths:
            for edge in subpath["edges"]:
                concat = str(edge[0]) + "_" + str(edge[1])
                if concat not in self.ifg:
                    self.ifg[concat] = (0 , self.cfg[edge[0]][edge[1]])

        # 2. Add orignal non-subpath constraints with Ie = [f(e), f(e)]
        for u in self.cfg:
            for dest in self.cfg[u].keys():
                concat = str(u) + "_" + str(dest)
                if concat not in self.ifg:
                    flow = self.cfg[u][dest]
                    self.ifg[concat] = (flow, flow)

        # 3. Add node s' w/ edge (s',s) and I = [|f(e)|,|f(e)|]
        # find the total flow of G
        total_flow = 0
        for dest in self.cfg[0]:
            total_flow += self.cfg[0][dest]
        # add node
        self.new_source = self.new_node()
        concat = str(self.new_source) + "_0" # assumes that 0 is the existing source
        self.ifg[concat] = (total_flow, total_flow)

        # 4. For each subpath constraint Ri create ndoes xi and yi
        for subpath in self.subpaths:
            xi = self.new_node()
            yi = self.new_node()
            # assumes that the edges are already in order
            concat = str(subpath["edges"][0][0]) + "_" + str(xi) # edge (wi,xi)
            self.ifg[concat] = (0, float("inf"))
            concat = str(yi) + "_" + str(subpath["edges"][-1][1]) # edge (yi, zi)
            self.ifg[concat] = (0, float("inf"))
            concat = str(xi) + "_" + str(yi)
            self.ifg[concat] = (subpath["demand"], float("inf"))
            subpath["constraint_edge_nodes"] = (xi,yi)
            
            # track subpath change to undo later
            #  (w,x) -> [w]
            #  (y,z) -> []
            #  (x,y) -> [everything between w and z in the original]
            concat = str(subpath["edges"][0][0]) + "_" + str(xi) # edge (wi,xi)
            self.subpath_map[concat] = [subpath["edges"][0][0]]
            concat = str(yi) + "_" + str(subpath["edges"][-1][1]) # edge (yi, zi)
            self.subpath_map[concat] = []
            concat = str(xi) + "_" + str(yi) # edge (xi, yi)
            nodes = []
            for e in subpath["edges"][1:-1]:
                nodes.append(e[0])
            nodes.append(subpath["edges"][-1][0])
            self.subpath_map[concat] = nodes

        # 5A. Find consecutive subpaths 
        # To be consecutive they must overlap (share an edge) and 
        # there can't be another subpath connecting them in the middle
        overlapping_subpaths = { new_dict : [] for new_dict in range(len(self.subpaths))}
        for i in range(len(self.subpaths)):
            for j in range(i+1, len(self.subpaths)):
                for edge in self.subpaths[i]["edges"]:
                    if edge in self.subpaths[j]["edges"]:
                        overlapping_subpaths[i].append(j)
        # check for transitive subpaths
        for subpath in overlapping_subpaths:
            # for each of the other subpaths that this one overlaps
            for primary_overlap in overlapping_subpaths[subpath]:
                # check that it it can't be immediately reached by another overlapping subpath
                for secondary_overlap in overlapping_subpaths[subpath]:
                    if primary_overlap == secondary_overlap:
                        continue
                    # if it is accessible then remove it
                    if primary_overlap in overlapping_subpaths[secondary_overlap]:
                        overlapping_subpaths[secondary_overlap].remove(primary_overlap)

        # 5B. Connect each pair of consecutive subpaths (yi, xj) with I = [0, inf)
        for overlap_i in overlapping_subpaths:
            for overlap_j in overlapping_subpaths[overlap_i]:
                concat = str(self.subpaths[overlap_i]["constraint_edge_nodes"][1]) + "_" + \
                    str(self.subpaths[overlap_j]["constraint_edge_nodes"][0])
                self.ifg[concat] = (0, float("inf"))
                # also track overlap to undo later
                self.subpath_map[concat] = []

    def new_node(self):
        """ Returns the ID of a new unique node
        """
        new_node = (max(self.nodes) + 1)
        self.nodes.append(new_node)
        return new_node

    def undo_subpaths(self, paths):
        """ Returns provided paths after replacing subpath nodes with their original nodes
        """
        print("Paths to undo:", paths)
        new_paths = []
        for path in paths:
            new_path = []
            for x in range(len(path)-1):
                concat = str(path[x]) + "_" + str(path[x+1])
                if concat in self.subpath_map.keys():
                    original_nodes = self.subpath_map[concat]
                    new_path += original_nodes
                else:
                    new_path.append(path[x])
            new_path.append(path[-1])
            new_paths.append(new_path)
        return new_paths

class DeBruijnGraph:
    """This represents a DeBruijn Graph, where the nodes encode 
    a list of symbols. In this case the nodes represent sequences 
    genetic information. 
    """
    def __init__(self, k = 4):
        self.k = k # the size of the k-mers
        self.vertexes = [] # maps index to original sequence value

        # Maps node to other nodes with frequency. 
        # In the form {u : {v1 : f1, v2 : f2, ...}, ...}
        self.edges = dict()

        # Space separated subpath, where the values are the nodes (not sequence)
        self.constraints = []

    def add_sequence(self, seq):
        """Takes in a sequence and adds its content
        """
        # get all k-mers
        k_mers = []
        for x in range(len(seq)-(self.k-1)):
            k_mers.append(seq[x:x+self.k])

        # get all k-1-mers and their edges
        for mer in k_mers:
            l_mer = mer[:-1]
            r_mer = mer[1:]

            # make sure the k-1-mers have a number
            if l_mer not in self.vertexes:
                self.vertexes.append(l_mer)
            if r_mer not in self.vertexes:
                self.vertexes.append(r_mer)

            # add the edge between them
            l_mer_index = self.vertexes.index(l_mer)
            r_mer_index = self.vertexes.index(r_mer)
            # if the left k-1-mer is not added yet: trivial
            if l_mer_index not in self.edges:
                self.edges[l_mer_index] = {r_mer_index: 1}
            # otherwise see if the right k-1-mer has been added
            else:
                if r_mer_index not in self.edges[l_mer_index]:
                    self.edges[l_mer_index][r_mer_index] = 1
                else:
                    # if it already exists, just increment the flow
                    self.edges[l_mer_index][r_mer_index] = self.edges[l_mer_index][r_mer_index] + 1

    def add_subpath(self, subpath):
        """Takes in a subpath sequence and creates a space separated 
        series of nodes with their associated demands
        """
        # get all k-1-mers
        k_1_mers = []
        for x in range(len(subpath)-(self.k-2)):
            k_1_mers.append(subpath[x:x+(self.k-1)])

        # get the node order of the subpath sequence
        seq = ""
        for mer in k_1_mers:
            index = self.vertexes.index(mer)
            seq += str(index) + " "

        # add a default demand for now
        seq += "1.00"   

        self.constraints.append(seq)

    def get_flow_graph(self):
        """Returns the DeBruijnGraph as a Graph that can
        be used in the IFD program
        """
        num_nodes = len(self.vertexes)
        flow_graph = FlowGraph(num_nodes)

        # add all edges
        for u in self.edges.keys():
            for v in self.edges[u]:
                flow_graph.add_edge(u,v,self.edges[u][v])

        # add subpaths
        for subpath in self.constraints:
            flow_graph.add_subpath(subpath)

        return flow_graph

    def convert(self, nodes):
        """Takes in nodes and returns the original sequence
        """
        sequence = self.vertexes[nodes[0]]
        for i in range(1,len(nodes)):
            sequence += self.vertexes[nodes[i]][-1]
        return sequence
