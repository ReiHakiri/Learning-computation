def all_lists(domain: list, n: int):
    if n == 0:
        yield []

    else:
        for l in all_lists(domain, n - 1):
            for element in domain:
                yield l + [element]

class Statement:
    """
    Abstract class
    """
    def evaluate(self, l: list[bool]):
        raise NotImplementedError()

    def n_atomics(self):
        """
        Precondition: have numbers for atomic propositions up to some number,
        call this ordered naming
        """
        raise NotImplementedError()

    def is_tautology(self):
        """
        Precondition: uses ordered naming
        """
        n = self.n_atomics()

        for assignment in all_lists([True, False], n):
            if not self.evaluate(assignment):
                return False

        return True

    def sat(self):
        """
        Precondition: uses ordered naming
        """
        n = self.n_atomics()

        for assignment in all_lists([True, False], n):
            if self.evaluate(assignment):
                return assignment

        return None

class Atomic(Statement):
    def __init__(self, n: int):
        self.n = n

    def n_atomics(self):
        return self.n + 1

    def evaluate(self, l: list[bool]):
        """
        Precondition: 0 <= self.n < len(l)
        """
        return l[self.n]

class Not(Statement):
    def __init__(self, phi: Statement):
        self.phi = phi

    def n_atomics(self):
        return self.phi.n_atomics()

    def evaluate(self, l: list[bool]):
        return not self.phi.evaluate(l)

class And(Statement):
    def __init__(self, phi: Statement, tau: Statement):
        self.phi = phi
        self.tau = tau

    def n_atomics(self):
        return max(self.phi.n_atomics(), self.tau.n_atomics())

    def evaluate(self, l: list[bool]):
        return self.phi.evaluate(l) and self.tau.evaluate(l)

class Or(Statement):
    def __init__(self, phi: Statement, tau: Statement):
        self.phi = phi
        self.tau = tau

    def n_atomics(self):
        return max(self.phi.n_atomics(), self.tau.n_atomics())

    def evaluate(self, l: list[bool]):
        return self.phi.evaluate(l) or self.tau.evaluate(l)

class If(Statement):
    def __init__(self, phi: Statement, tau: Statement):
        self.phi = phi
        self.tau = tau

    def n_atomics(self):
        return max(self.phi.n_atomics(), self.tau.n_atomics())

    def evaluate(self, l: list[bool]):
        if self.phi.evaluate(l):
            return self.tau.evaluate(l)

        else:
            return True

class Iff(Statement):
    def __init__(self, phi: Statement, tau: Statement):
        self.phi = phi
        self.tau = tau

    def n_atomics(self):
        return max(self.phi.n_atomics(), self.tau.n_atomics())

    def evaluate(self, l: list[bool]):
        return self.phi.evaluate(l) == self.tau.evaluate(l)

true_enc = If(Atomic(0), Atomic(0))

print(true_enc.is_tautology())

false_enc = Not(true_enc)

print(false_enc.is_tautology())

generating_tautology = Iff(And(If(Iff(Atomic(2), true_enc), Iff(Atomic(1), true_enc)), If(Iff(Atomic(2), false_enc), Iff(Atomic(1), true_enc))), Atomic(1))

print(generating_tautology.is_tautology())

contingent = Iff(And(Atomic(0), Atomic(1)), Or(Atomic(2), If(Atomic(0), Atomic(3))))

print(contingent.is_tautology(), contingent.sat())

class Argument:
    def __init__(self, premises: list[Statement], conclusion: Statement):
        self.premises = premises
        self.conclusion = conclusion

    def to_statement(self):
        if len(self.premises) == 0:
            return self.conclusion

        antecedent = self.premises[0]

        for premise in self.premises[1:]:
            antecedent = And(antecedent, premise)

        return If(antecedent, self.conclusion)

    def is_valid(self):
        return self.to_statement().is_tautology()

premises_eg = [Atomic(0), Atomic(1), Iff(Atomic(0), Atomic(2)), Or(Atomic(2), Atomic(3))]
conclusion_eg = If(And(Atomic(0), Atomic(1)), Atomic(2))

print(Argument(premises_eg, conclusion_eg).is_valid())

premises_eg =[]
conclusion_eg = Atomic(0)

print(Argument(premises_eg, conclusion_eg).is_valid())