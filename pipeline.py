"""Creates and runs the pipline

author: Sage Acteson
"""

from src.storage import FlowGraph, DeBruijnGraph
from src.graph_solver import GraphSolver
from src.read_strategy import Context, ReadFASTA, ReadFASTQ

import sys

class Pipeline:
    """Has all the components to run the main tasks necessary
    to take in reads and find the original sequence
    """
    def __init__(self, file_names):
        self.file_names = file_names # (short reads, subpaths)
        self.short_reads = None
        self.long_reads = None
        self.deb_graph = None # debruijn graph
        self.solver = None # graph solver
        self.solutions = [] # list of sequences

    def run(self):
        """This runs all the key steps in the pipeline
        """
        self.read_short_reads()
        self.read_long_reads()
        self.create_graph()
        self.prepare_graph()
        self.solve_graph()
        self.extract_sequences()
        self.write_solutions()

    def read_short_reads(self):
        """Read in the short reads from the appropriate file
        """
        file_type = self.file_names[0].split(".")[-1]
        context = Context()
        context.determine_read_strategy(file_type)
        short_stored_reads = context.execute_read_strategy(self.file_names[0])
        self.short_reads = short_stored_reads.get_reads()

    def read_long_reads(self):
        """Read in the long reads from the appropriate file
        """
        file_type = self.file_names[1].split(".")[-1]
        context = Context()
        context.determine_read_strategy(file_type)
        long_stored_reads = context.execute_read_strategy(self.file_names[1])
        self.long_reads = long_stored_reads.get_reads()

    def create_graph(self):
        """Create a DeBruijn graph from the short and long reads
        """
        # init graph
        self.deb_graph = DeBruijnGraph(5)

        # add sequences from short reads
        for seq in self.short_reads:
            self.deb_graph.add_sequence(seq)
        
        # add in subpaths
        for seq in self.long_reads:
            self.deb_graph.add_subpath(seq)

    def prepare_graph(self):
        """Convert the DeBruijn graph to a flow graph and prepare 
        the solver
        """
        flow_graph = self.deb_graph.get_flow_graph()
        self.solver = GraphSolver(flow_graph)

    def solve_graph(self):
        """Call on the graph solver to find a solution
        """
        self.solver.solve()

    def extract_sequences(self):
        """Use the solver (which has the Debruijn grpah with the encoding info)
        to decode the solution
        """
        solutions = self.solver.ifd_solution
        weights = self.solver.ifd_weights
        for sol in range(len(solutions)):
            sequence = self.deb_graph.convert(solutions[sol])
            sequence += " " + str(weights[sol]) + "\n"
            self.solutions.append(sequence)

    def write_solutions(self):
        """Write the found solutions to an output file
        """
        # take the name of the short read file and add _solution.txt
        title = self.file_names[0].split(".")[0] + "_solution.txt"
        f = open(title, 'w')
        f.writelines(self.solutions)
        f.close()

if __name__ == "__main__":
    # Parse command line input
    graph_file = sys.argv[1]
    subpath_file = sys.argv[2]

    pipeline = Pipeline((graph_file,subpath_file))
    pipeline.run()