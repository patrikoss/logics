from z3 import And, Or, Not, Implies, Solver, sat, Bool

class Variable():
    def __init__(self):
        pass

class X(Variable):
    def __init__(self, step, state):
        self.step = step
        self.state = state

    def __str__(self):
        return 'x_{}_{}'.format(step, state)

class TMAcceptanceSAT():

    def __init__(self, alphabet, states, transitions, initState, acceptingState,word):
        """
        alphabet: list of characters
        states: list of states
        transitions: mappings of (state,char) -> (state, char, direction)
        initState: initial state of the turing machine
        acceptingState: accepting state of the turing machine
        word: input word for which to check whether the machine accepts it or not
        """

        self.alphabet = alphabet
        self.states = states
        self.transitions = transitions
        self.initState = initState
        self.acceptingState = acceptingState
        self.word = word

    def generateSAT(self):
        """
        Returns the SAT for a problem of word acceptance of a given
        Turing Machine with constraints that:
        - machine operates only on the cells occupied by the initial input word
        - machine makes at most |w| steps, where w is an input word
        """
        conditions = [
            self._formulasInitial,
            self._formulasNoMultipleStates,
            self._formulasReachAcceptingState,
            self._formulasNoMultipleCharacters,
            self._formulasNoMultipleHeadPositions,
            self._formulasValidTransitions,
            self._formulasNonHeadCharsNonModifiable
        ]
        sat = []
        for cond in conditions:
            sat.extend(cond())
        return And(sat)

    def solveSAT(self, satFormula):
        """
        Runs a SAT solver for a given SAT formula, and returns the valuation
        of the literals in case the sat formula is satisfiable.
        In case it is not satisfiable, the function returns empty list
        """
        satSolver = Solver()
        satSolver.add(satFormula)

        # return a satisfying assignment
        model = satSolver.model() if satSolver.check() == sat else []
        return dict((str(k),bool(model[k])) for k in model)

    def decodeSATOutput(self, valuation):
        """
        Returns the accepting run of the turing machine based on the valuation
        of solved sat variables
        """
        if valuation == []:
            return []
        xtempl = 'x_{}_{}'
        ytempl = 'y_{}_{}'
        ztempl = 'z_{}_{}_{}'

        stateHistory = []
        headPositionHistory = []
        tapeHistory = []
        for step in range(len(self.word)):
            # find the state at given step
            for state in self.states:
                stepState = xtempl.format(step, state)
                if valuation[stepState]:
                    stateHistory += stepState,
                    #break
            # find the machine head at given step
            for pos in range(len(self.word)):
                headPos = ytempl.format(step, pos)
                if valuation[headPos]:
                    headPositionHistory += headPos,
                    #break
            # find the tape content at given step
            tapeHistory += [],
            for pos in range(len(self.word)):
                for char in self.alphabet:
                    stepCellChar = ztempl.format(step, pos, char)
                    if valuation[stepCellChar]:
                        tapeHistory[-1] += stepCellChar,
                        #break
            if stateHistory[-1] == self.acceptingState:
                break
        return list(zip(stateHistory, headPositionHistory, tapeHistory))


    def _formulasNoMultipleStates(self):
        """
        Generate SAT formulas that satisfy the rule that:
        For every point in time, the machine is in at most 1 state
        """
        formulas = []
        # x_i_q is True iff at step i the machine is in state q
        x = "x_{}_{}"
        for step in range(len(self.word)):
            for q1 in range(len(self.states)):
                for q2 in range(q1+1, len(self.states)):
                    formulas += Not(
                        And([
                            Bool(x.format(step, self.states[q1])),
                            Bool(x.format(step, self.states[q2])),
                        ])
                    ),
        return [And(formulas)]

    def _formulasNoMultipleHeadPositions(self):
        """
        Generate SAT formulas that satisfy the rule that:
        For every point in time, the machine head is in at most 1 position
        """
        formulas = []
        # y_i_k is True iff at step i the machine head is at position k
        y = "y_{}_{}"
        for step in range(len(self.word)):
            for pos1 in range(len(self.word)):
                for pos2 in range(pos1+1, len(self.word)):
                    formulas += Not(
                        And([
                            Bool(y.format(step, pos1)),
                            Bool(y.format(step, pos2))
                        ])
                    ),
        return [And(formulas)]

    def _formulasNoMultipleCharacters(self):
        """
        Generate SAT formulas that satisfy the rule that:
        For every point in time, and every cell, there is at most 1 character
        in this cell
        """
        formulas = []
        # z_i_k_c - True iff at step i, and cell position k, the character in
        #       the cell is c
        # y_i_k is True iff at step i the machine head is at position k
        # x_i_q is True iff at step i the machine is in state q
        z = "z_{}_{}_{}"
        y = "y_{}_{}"
        x = "x_{}_{}"
        for step in range(len(self.word)):
            for pos in range(len(self.word)):
                for char1 in range(len(self.alphabet)):
                    for char2 in range(char1+1, len(self.alphabet)):
                        formulas += Not(
                            And([
                                Bool(z.format(step, pos, self.alphabet[char1])),
                                Bool(z.format(step, pos, self.alphabet[char2])),
                            ])
                        ),
        return [And(formulas)]

    def _formulasNonHeadCharsNonModifiable(self):
        formulas = []
        z = "z_{}_{}_{}"
        y = "y_{}_{}"
        x = "x_{}_{}"
        for step in range(len(self.word)-1):
            for pos in range(len(self.word)):
                for char in self.alphabet:
                    formulas += Implies(
                        And([
                            Not(Bool(y.format(step, pos))),
                            Bool(z.format(step,pos,char))
                        ]),
                        Bool(z.format(step+1, pos, char))
                    ),
        return [And(formulas)]


    def _formulasValidTransitions(self):
        """
        Generate SAT formulas that can be deduced by the configuration
        of the machine in a given step i to form a new configuration of
        machine at step i+1
        """
        formulas = []
        # z_i_k_c - True iff at step i, and cell position k, the character in
        #       the cell is c
        # y_i_k is True iff at step i the machine head is at position k
        # x_i_q is True iff at step i the machine is in state q
        z = "z_{}_{}_{}"
        y = "y_{}_{}"
        x = "x_{}_{}"
        for step in range(len(self.word)-1):
            for pos in range(len(self.word)):
                for state in self.states:
                    for char in self.alphabet:
                        antecedent = And([
                            Bool(x.format(step, state)),
                            Bool(y.format(step, pos)),
                            Bool(z.format(step, pos, char))
                        ])
                        # generate the consequent
                        consequent = []
                        for transition in self.transitions.get((state, char), []):
                            dstState, dstChar, direction = transition
                            # only the transitions which operate on original
                            # cells are allowed
                            if 0 <= pos + direction < len(self.word):
                                consequent += And([
                                    Bool(x.format(step+1, dstState)),
                                    Bool(y.format(step+1, pos+direction)),
                                    Bool(z.format(step+1, pos, dstChar)),
                                ]),
                        if len(consequent) > 0:
                            consequent = Or(consequent)
                            formulas += Implies(antecedent, consequent),
        return [And(formulas)]

    def _formulasReachAcceptingState(self):
        """
        Generate SAT formulas that satisfy the rule that:
        For some point in time, the machine reaches the accepting state
        """
        formulas = []
        # x_i_q is True iff at step i the machine is in state q
        x = "x_{}_{}"
        for step in range(len(self.word)):
            formulas += Bool(x.format(step, self.acceptingState)),
        return [Or(formulas)]

    def _formulasInitial(self):
        """
        Generate initial SAT formulas that correspond to the given input.
        """
        formulas = []
        x = "x_{}_{}"
        y = "y_{}_{}"
        z = "z_{}_{}_{}"
        formulas += Bool(x.format(0, self.initState)),
        formulas += Bool(y.format(0, 0)),
        for pos in range(len(self.word)):
            formulas += Bool(z.format(0,pos,self.word[pos])),
        return [And(formulas)]



if __name__=='__main__':
    (k, n, m) = map(int, raw_input().split())
    alphabet = raw_input().split()
    states = raw_input().split()
    initState = raw_input()
    acceptingState = raw_input()
    transitions = dict()
    for _ in range(m):
        cFrom, qFrom, cTo, qTo, direction = raw_input().split()
        transitions.setdefault((qFrom,cFrom), [])
        transitions[(qFrom, cFrom)] += (qTo, cTo, int(direction)),
    l = int(raw_input())
    word = raw_input().split()

    tmsat = TMAcceptanceSAT(alphabet, states, transitions, initState, acceptingState,word)
    formulas = tmsat.generateSAT()
    #print formulas
    valuation = tmsat.solveSAT(formulas)
    hist = tmsat.decodeSATOutput(valuation)
    for step in hist:
        print(step)
