from __future__ import print_function
from z3 import *


def model(phi):
    
    # create a SAT instance
    s = Solver()
    s.add(phi)
    
    # return a satisfying assignment
    return s.model() if s.check() == sat else ["unsat"]

class StartIndex():
    """
    Starting index for a sequence of marked fields withing a row or column
    """
    template = "start_{vector_name}_{vector_number}_{index}"

    def __init__(self, vector_name, vector_number, index):
        self.vector_name = vector_name
        self.vector_number = vector_number
        self.index = index

    def int(self):
        return Int(str(self))

    def __str__(self):
        return StartIndex.template.format(vector_name=self.vector_name, vector_number = self.vector_number, index = self.index)
   
class NonogramFormulasGenerator():

    def __init__(self, rows, cols):
        self.rows = self._prepare_vectors(rows, 'row')
        self.cols = self._prepare_vectors(cols, 'col')

    def _prepare_vectors(self, vectors, vector_name):
        """
        Transforms given columns or rows from the form specifying only the lengths
        of the subsequent checked fields to the form of a tuple where the
        first element of the tuple specify the starting position of a subsequent
        checked fields, and the second specify the length of these subsequent
        checked fields
        """
        result = []
        for vector in range(len(vectors)):
            lengths = vectors[vector]
            starts = [StartIndex(vector_name, vector, index).int() for index in range(len(lengths))]
            result.append( zip(starts, lengths) )
        return result 

    def _generate_sequence_columns_formulas(self, cols, f):
        """
        Generates formulas for columns, so that the function f satisfy
        the conditions that there are as many sequence of true elements
        as specified in the input for a specified column, and their lengths match
        those specified in the input.  
        """
        x = Int('x')
        formulas = []
        for col_nr, col in enumerate(cols):
            col_formulas = []
            for i, (start_pos, length) in enumerate(col):
                col_formulas += ForAll( [x], Implies( And(x >= start_pos, x < start_pos + length), f(x, col_nr) == True) ) ,
                col_formulas += f(start_pos+length, col_nr) == False,
                if i == 0:
                    col_formulas += start_pos >= 0,
                else:
                    prev_start_pos, prev_length = col[i-1]
                    col_formulas += prev_start_pos+prev_length < start_pos,
                if i == len(col) - 1:
                    col_formulas += start_pos + length <= len(self.rows),

            formulas += [And(col_formulas)] 
        return And(formulas)

    def _generate_sequence_rows_formulas(self, rows, f):
        """
        Generates formulas for rows, so that the function f satisfy
        the conditions that there are as many sequence of true elements
        as specified in the input for a specified row, and their lengths match
        those specified in the input.  
        """
        x = Int('x')
        formulas = []
        for row_nr, row in enumerate(rows):
            row_formulas = []
            for i, (start_pos, length) in enumerate(row):
                row_formulas += ForAll( [x], Implies( And(x >= start_pos, x < start_pos + length), f(row_nr, x) == True) ) ,
                row_formulas += f(row_nr, start_pos+length) == False,
                if i == 0:
                    row_formulas += start_pos >= 0,
                else:
                    prev_start_pos, prev_length = row[i-1]
                    row_formulas += prev_start_pos+prev_length < start_pos,
                if i == len(row) - 1:
                    row_formulas += start_pos + length <= len(self.cols),

            formulas += [And(row_formulas)] 
        return And(formulas)

    def _generate_sum_check_rows(self, f):
        """
        Generates formulas for the function f that satisfy the condition
        that the sum of 'true' elements for function f for a given row
        sums up to the input sum for that row
        """
        formulas = []
        for row_nr, row in enumerate(self.rows):
            s = sum(length for start, length in row)
            formulas += [ Sum([If(f(row_nr,col_nr), 1, 0) for col_nr in range(len(self.cols))] ) == s ]
        return And(formulas)

    def _generate_sum_check_columns(self, f):
        """
        Generates formulas for the function f that satisfy the condition
        that the sum of 'true' elements for function f for a given column
        sums up to the input sum for that column
        """
        formulas = []
        for col_nr, col in enumerate(self.cols):
            s = sum(length for start, length in col)
            formulas += [ Sum([If(f(x,col_nr), 1, 0) for x in range(len(self.rows))] ) == s ]
        return And(formulas)
            
    def generate_all_formulas(self, f):
        return And(self._generate_sequence_rows_formulas(self.rows, f),\
            self._generate_sum_check_rows(f),\
            self._generate_sum_check_columns(f),\
            self._generate_sequence_columns_formulas(self.cols, f))

def get_solution(rows, cols):
    """
    Returns one of the following:
    - 'many solutions' - if the given nonogram has more than 1 valid solution
    - 'unsolvable' if the given nongram is invalid
    - definition of a nonogram where '#' denotes the marked field,
        while '.' denotes an unmarked field
    """
    nonogram = NonogramFormulasGenerator(rows, cols)
    f = Function('f', IntSort(), IntSort(), BoolSort())
    formulasF = nonogram.generate_all_formulas(f)
    modelF = model(formulasF)
    if modelF == ['unsat']:
        return 'unsolvable'

    # at this point we know we have at least one solution
    # check if there is a second by negating the first solution
    alternative_function_formulas = []
    g = Function('g', IntSort(), IntSort(), BoolSort())
    formulasG = nonogram.generate_all_formulas(g)
    for row in range(len(rows)):
        for col in range(len(cols)):
            alternative_function_formulas += modelF.eval(f(row,col)) != g(row,col),
    alternative_function_formulas = Or(alternative_function_formulas)
    formulasG = And(alternative_function_formulas, formulasG)
    modelG = model(formulasG)
    if modelG != ['unsat']:
        return 'many solutions'

    # return the only solution
    sol = ''
    for row in range(len(rows)):
        for col in range(len(cols)):
            sol += '#' if modelF.eval(f(row, col)) else '.'
        sol += '\n' if row != len(rows) -1 else ''
    return sol



def main():
    COLUMNS, ROWS = [int(x) for x in raw_input().split()]
    rows, cols = [], []
    for row in range(ROWS):
        rows.append( [int(x) for x in raw_input().split()][:-1] )
    for col in range(COLUMNS):
        cols.append( [int(x) for x in raw_input().split()][:-1] )
    
    print(get_solution(rows, cols))

if __name__=='__main__':
    main()
