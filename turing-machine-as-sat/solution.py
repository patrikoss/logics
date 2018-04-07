from z3 import And, Or, Not, Implies, Solver, sat, Bool

class X():
    """
    Literal in the target formula that is True iff
    at step i, the machine is in state q
    """
    template = "x_{i}_{q}"

    def __init__(self, step, state):
        self.step = step
        self.state = state

    def bool(self):
        return Bool(str(self))

    def __str__(self):
        return X.template.format(i=self.step,q=self.state)

class Y():
    """
    Literal in the taget formula that is True iff
    at step i the machine head is at position k
    """
    template = "y_{i}_{k}"

    def __init__(self, step, pos):
        self.step = step
        self.pos = pos

    def bool(self):
        return Bool(str(self))

    def __str__(self):
        return Y.template.format(i=self.step,k=self.pos)

class Z():
    """
    Literal in the target formula that is True iff
    at step i, and cell position k, the character is in the cell is c
    """
    template = "z_{i}_{k}_{c}"

    def __init__(self, step, pos, char):
        self.step = step
        self.pos = pos
        self.char = char

    def bool(self):
        return Bool(str(self))

    def __str__(self):
        return Z.template.format(i=self.step,k=self.pos,c=self.char)


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
        if len(valuation) == 0:
            return []

        stateHistory = []
        headPositionHistory = []
        tapeHistory = []
        for step in range(len(self.word)):
            # find the state at given step
            for state in self.states:
                if valuation[str(X(step, state))]:
                    stateHistory += state,
                    break

            # find the machine head at given step
            for pos in range(len(self.word)):
                if valuation[str(Y(step, pos))]:
                    headPositionHistory += pos,
                    break

            # find the tape content at given step
            tapeHistory += [],
            for pos in range(len(self.word)):
                for char in self.alphabet:
                    if valuation[str(Z(step, pos, char))]:
                        tapeHistory[-1] += (pos, char),
                        break

            if stateHistory[-1] == self.acceptingState:
                break

        # format the output
        history = []
        for step in range(len(stateHistory)):
            tapeContent = [c+'| ' for (_,c) in tapeHistory[step]]
            state = stateHistory[step]
            headPosition = headPositionHistory[step]

            tapeContent[headPosition] = tapeContent[headPosition][:-1]+state
            tapeContent = ' '.join(tapeContent)
            history.append(tapeContent)
        return history

    def _formulasNoMultipleStates(self):
        """
        Generate SAT formulas that satisfy the rule that:
        For every point in time, the machine is in at most 1 state
        """
        formulas = []
        for step in range(len(self.word)):
            for q1 in range(len(self.states)):
                for q2 in range(q1+1, len(self.states)):
                    formulas += Not(
                        And([
                            X(step, self.states[q1]).bool(),
                            X(step, self.states[q2]).bool(),
                        ])
                    ),
        return [And(formulas)]

    def _formulasNoMultipleHeadPositions(self):
        """
        Generate SAT formulas that satisfy the rule that:
        For every point in time, the machine head is in at most 1 position
        """
        formulas = []
        for step in range(len(self.word)):
            for pos1 in range(len(self.word)):
                for pos2 in range(pos1+1, len(self.word)):
                    formulas += Not(
                        And([
                            Y(step, pos1).bool(),
                            Y(step, pos2).bool()
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
        for step in range(len(self.word)):
            for pos in range(len(self.word)):
                for char1 in range(len(self.alphabet)):
                    for char2 in range(char1+1, len(self.alphabet)):
                        formulas += Not(
                            And([
                                Z(step, pos, self.alphabet[char1]).bool(),
                                Z(step, pos, self.alphabet[char2]).bool(),
                            ])
                        ),
        return [And(formulas)]

    def _formulasNonHeadCharsNonModifiable(self):
        formulas = []
        for step in range(len(self.word)-1):
            for pos in range(len(self.word)):
                for char in self.alphabet:
                    formulas += Implies(
                        And([
                            Not(Y(step, pos).bool()),
                            Z(step,pos,char).bool()
                        ]),
                        Z(step+1, pos, char).bool()
                    ),
        return [And(formulas)]


    def _formulasValidTransitions(self):
        """
        Generate SAT formulas that can be deduced by the configuration
        of the machine in a given step i to form a new configuration of
        machine at step i+1
        """
        formulas = []
        for step in range(len(self.word)-1):
            for pos in range(len(self.word)):
                for state in self.states:
                    for char in self.alphabet:
                        antecedent = And([
                            X(step, state).bool(),
                            Y(step, pos).bool(),
                            Z(step, pos, char).bool()
                        ])
                        # generate the consequent
                        consequent = []
                        for transition in self.transitions.get((state, char), []):
                            dstState, dstChar, direction = transition
                            # only the transitions which operate on original
                            # cells are allowed
                            if 0 <= pos + direction < len(self.word):
                                consequent += And([
                                    X(step+1, dstState).bool(),
                                    Y(step+1, pos+direction).bool(),
                                    Z(step+1, pos, dstChar).bool(),
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
        for step in range(len(self.word)):
            formulas += X(step, self.acceptingState).bool(),
        return [Or(formulas)]

    def _formulasInitial(self):
        """
        Generate initial SAT formulas that correspond to the given input.
        """
        formulas = []
        formulas += X(0, self.initState).bool(),
        formulas += Y(0, 0).bool(),
        for pos in range(len(self.word)):
            formulas += Z(0,pos,self.word[pos]).bool(),
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
    valuation = tmsat.solveSAT(formulas)
    history = tmsat.decodeSATOutput(valuation)
    if history == []:
        print("NO")
    else:
        print("YES\n")
        for configuration in history:
            print(configuration)
