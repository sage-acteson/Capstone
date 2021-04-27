"""Written by Lucy Williams
https://github.com/msu-alglab/coaster/blob/master/ifd_package/flows/ifd.py
"""
import time


class InexactFlowInstance():
    """
    Inexact Flow Decomposition instance.

    Takes in an ifd graph.

    TODO: description
    ----------
    Attributes:
    TODO
    """
    def __init__(self, graph, silent=True):
        # self.graph is a IfdAdjList object
        self.graph = graph
        self.silent = silent
        self.reduced, self.mapping = graph.contracted()

    def is_trivial(self):
        return len(self.reduced) <= 1

    def solve(self):
        """Find an inexact path decomposition (if one exists)."""
        # set up and find maxflow problem
        start_time = time.time()
        found_flow = self.graph.update_flow()
        print("After maxflow to find flow, graph is:")
        self.graph.print_out()
        print("\nMaxflow approach to find flow success? {}".format(found_flow))
        if found_flow:
            find_feasible_flow_time = time.time()-start_time
            print("Time to find initial flow: {}".
                  format(find_feasible_flow_time))

            # run heuristic 1
            start_time = time.time()
            if self.graph.get_num_zero_lower_bounds() > 0:
                print("\n>=1 edge wth lower bound 0. Running heuristic 1.")
                heuristic_1_updates = self.graph.run_heuristic_1()
            else:
                print("\n0 edges with lower bound 0, so skipping heuristic 1.")
                heuristic_1_updates = 0
            time_to_do_heuristic_1 = time.time() - start_time
            print("Time to run heuristic 1: {}".format(time_to_do_heuristic_1))

            start_time = time.time()
            self.graph.run_greedy_width()
            print("Time to run greedy width: {}".
                  format(time.time()-start_time))

            # get initial solution size
            init_k_pred = len(self.graph.get_paths())

            # run rebalancing + splice and merge
            print("\nStarting path rebalancing + splice/merge.")
            start_time = time.time()
            self.graph.path_splice()
            splice_time = time.time() - start_time
            print("Time to rebalance/splice paths: {}".format(splice_time))
            print("\nFinished rebalancing/splicing.")
            self.graph.print_paths()

            """

            print("\nStarting pairwise rebalancing.")
            start_time = time.time()
            self.graph.pairwise_rebalance()
            pairwise_rebalancing_time = time.time() - start_time
            print("Time to do pairwise rebalancing: {}".format(
                                pairwise_rebalancing_time))
            print("\nFinished pairwise rebalancing.")
            self.graph.print_paths()

            print("\nStarting pairwise splicing.")
            start_time = time.time()
            self.graph.pairwise_splice()
            pairwise_splicing_time = time.time() - start_time
            print("Time to do pairwise splicing: {}".format(
                                        pairwise_splicing_time))
            print("\nFinished pairwise splicing.")
            self.graph.print_paths()

            """

            # get metrics
            found_k = self.graph.get_k()
            splices = self.graph.get_splices()
            overlaps = self.graph.get_overlap_count()
            rebalances = self.graph.get_rebalances()
            pairwise_rebalances = self.graph.get_pairwise_rebalances()
            pairwise_splices = self.graph.get_pairwise_splices()
            zero_intervals = self.graph.count_paths_with_zero_intervals()

            # check that solution is valid
            start_time = time.time()
            self.graph.check_flow()
            self.graph.check_paths()
            self.graph.check_conservation_of_flow()
            check_time = time.time()-start_time
            print("Time to check that solution is valid: {}".
                  format(check_time))
        else:
            # set variables to None that did not get set
            init_k_pred = 0
            rebalances = 0
            splices = 0
            overlaps = 0
            pairwise_rebalances = 0
            pairwise_splices = 0
            zero_intervals = 0
            heuristic_1_updates = None
            found_k = None
            splice_time = None
            check_time = None
            num_not_in_interval = None
            time_to_do_heuristic_1 = None
            find_feasible_flow_time = None
