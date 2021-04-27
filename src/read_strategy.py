"""This uses a Strategy Pattern that can be used to read in
different types of bioinformatic files that would contain 
information needed for this project.

author: Sage Acteson
"""

from abc import ABC, abstractmethod
from src.storage import StoredReads

class Context():
    def __init__(self, read_strategy = None):
        if read_strategy == None:
            self.read_strategy = ReadFASTA()
        else:
            self.read_strategy = read_strategy
    
    def execute_read_strategy(self, filename):
        return self.read_strategy.read_file(filename)

    def determine_read_strategy(self, file_type):
        """This determines which concrete strategy should be used.
        This is in the Context to eliminat redundant code in the pipline.py
        file. If this grows too large, possibly replace it with a factory pattern
        to generate the proper context or look into a registry:
        https://stackoverflow.com/questions/40591270/strategy-pattern-to-read-different-file-formats
        """
        strat = None
        if file_type == "fasta":
            strat = ReadFASTA()
        if file_type == "fastq":
            strat = ReadFASTQ()
        self.read_strategy = strat

class ReadStrategy(ABC):
    """Represents the Strategy interface. This is done with
    the Abstract  Base Class in Python.
    """
    @abstractmethod
    def read_file(self, file_name):
        pass

class ReadFASTA(ReadStrategy):
    """This strategy reads in a FASTA file. This is on of the 
    most common files and is in the following format:
    >Usually a title for the sequence
    ;Comments (rarely used)
            (can have extra whitespace)
    ACTGACTG  (the actual sequence)
            (more optional whitespace)

    Within a file there can be multiple lines in this order
    """
    def read_file(self, file_name):

        f = open(file_name)
        sequences = []
        for l in f:
            # check if this is an information line
            if l[0] == '>':
                continue
            # check if this is a comment
            elif l[0] == ';':
                continue
            else:
                x = l.strip()
                # check if there is actual content
                if len(x) == 0:
                    continue
                sequences.append(x)
        f.close()

        return StoredReads(sequences)

class ReadFASTQ(ReadStrategy):
    """This strategy reads in a FASTQ file which come in the 
    following format:

    @Header info about the sequence
    ACTGACTG (actual sequence)
    + (optional comment after required '+')
    (quality values for the sequence)
    
    Within a file there can be multiple lines in this order
    """
    def read_file(self, file_name):
        print("reading fastq file")

        f = open(file_name)
        sequences = []
        # boolean to tell if content is a sequence or quality value
        previous_was_plus = False
        for l in f:
            # check if this is an information line
            if l[0] == '@':
                previous_was_plus = False
                continue
            # check if this is a comment line
            if l[0] == '+':
                previous_was_plus = True
                continue
            if previous_was_plus:
                # This is quality values. Ignore for now.
                previous_was_plus = False
                continue
            
            x = l.strip()
            if len(x) == 0:
                continue
            sequences.append(x)
        f.close()

        return StoredReads(sequences)