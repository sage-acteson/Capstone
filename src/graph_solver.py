"""This handles solving flow graphs.

author: Sage Acteson
"""

from core.graphs import AdjList
from core.ifd.graphs import IfdAdjList
from core.ifd.ifd import InexactFlowInstance
from src.storage import FlowGraph

class GraphSolver:
    """
    This class handles content around finding a solution to a graph.
    Specifically this calls all the appropriate methods to take a flow graph,
    reduce it, then run IFD (inexact flow decomposition) on it.
    """

    def __init__(self, flow_graph):
        self.solver = None
        self.flow_graph = flow_graph
        self.reduced_graph = None # the flow_graph after being reduced ifd can run on it
        self.ifd_solution = None 
        self.ifd_weights = None # the weights of the ifd solutions

    def solve(self):
        self.reduce_graph()
        self.get_ifd_solution()

    def reduce_graph(self):
        """Reduces a flow graph to a valid IFD graph. The valid IFD
        graph is an AdjList.
        """
        self.flow_graph.apply_constraints()
        # convert the reduced graph to AdjList to pass to IFDSolver
        ifd_data = self.flow_graph.ifg # In the form { 'u_v' : (lb, ub)}
        ifd_graph = IfdAdjList()
        for k in ifd_data:
            u_v = k.split("_")
            ifd_graph.add_inexact_edge(int(u_v[0]),int(u_v[1]), float(ifd_data[k][0]),float(ifd_data[k][1]))
        self.reduced_graph = ifd_graph

        self.solver = InexactFlowInstance(self.reduced_graph)

    def get_ifd_solution(self):
        # get and solutions and convert as needed
        self.solver.solve()
        self.solver.graph.convert_paths() # converts from edges to nodes
        self.ifd_solution = self.flow_graph.undo_subpaths(self.solver.graph.get_converted_paths())
        self.ifd_weights = self.solver.graph.weights
