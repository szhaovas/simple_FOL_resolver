import re
import copy

num_vars_seen = 0
lower_case_letters = ['a','b','c','d','e','f','g','h','i','j','k','l','m','n','o','p','q','r','s','t','u','v','w','x','y','z']
first_promotion_threth = 26
second_promotion_threth = 26*26

# 0 -> 'aaa'
# 26 -> 'aba'
# 676 -> 'aab'
def standard_var_encode(num_vars_seen):
    third_quotient, third_remainder = divmod(num_vars_seen, second_promotion_threth)
    second_quotient, second_remainder = divmod(third_remainder, first_promotion_threth)
    third_digit = lower_case_letters[third_quotient]
    second_digit = lower_case_letters[second_quotient]
    first_digit = lower_case_letters[second_remainder]
    return first_digit+second_digit+third_digit

class Literal:
    def __init__(self, literal_str = None):
        self.predicate = None
        self.not_negated = None
        self.arg_list = []
        # FIXME: keep literal_str consistent with state
        self.literal_str = None
        if literal_str:
            # ~Predicate(A,x)
            psd = re.split('[(,)]', literal_str)[:-1]
            # ['~Predicate', 'A', 'x']
            if psd[0][0] == '~':
                self.predicate = psd[0][1:]
                self.not_negated = False
            else:
                self.predicate = psd[0]
                self.not_negated = True
            self.arg_list = psd[1:]
            self.literal_str = literal_str

    def negate(self):
        self.not_negated = not self.not_negated
        if self.literal_str[0] == '~':
            # from ~ to no ~
            self.literal_str = self.literal_str[1:]
        else:
            # from no ~ to ~
            self.literal_str = '~' + self.literal_str

    def to_string(self):
        return '~'[self.not_negated:] + self.predicate + '(' + ','.join(self.arg_list) + ')'

    def __str__(self):
        return self.literal_str

    __repr__ = __str__

    def __eq__(self, other):
        return self.literal_str == other.literal_str

    def __hash__(self):
        return hash(self.literal_str)

    # wrapper for unify
    #   checks if predicate name and len(arg_list) match
    def unify_with_other(self, other):
        '''
        x and y are arguments and can be string(constant/variable) or list(arg_list)
        theta is the substitution dictionary in this recursion level

        if can be unified
          returns something like {'aaa':'A', 'baa':'B'}
        else returns False

        assumes same predicate and len(arg_list)
        '''
        def unify(x, y, theta):
            if theta == False:
                return False
            elif x == y:
                return theta
            # if either is variable, try to assign the other to it
            elif isinstance(x, str) and x.islower():
                return unify_var(x, y, theta)
            elif isinstance(y, str) and y.islower():
                return unify_var(y, x, theta)
            # no Skolem functions, so no compound check
            # if both lists, recursively unify first then rest
            elif isinstance(x, list) and isinstance(y, list):
                return unify(x[1:], y[1:], unify(x[0], y[0], theta))
            else:
                return False

        # unify's helper
        #   checks for existing assignments
        #   var is variable
        def unify_var(var, x, theta):
            # if either already assigned, try to unify its assignment with the other
            if var in theta:
                return unify(theta[var], x, theta)
            elif x in theta:
                return unify(var, theta[x], theta)
            # no Skolem function so no occur-check needed
            # if neither assigned, assign x to var
            else:
                theta[var] = x
                return theta

        if self.predicate == other.predicate and len(self.arg_list) == len(other.arg_list):
            return unify(self.arg_list, other.arg_list, {})
        else:
            return False

'''
Need fast access according to predicate and negation
There can be multiple literals of the same predicate

disjunctive clause: {
                     'predicate1':
                        {
                            True:{literal1,literal2},
                            False:{literal3}
                        },
                     'predicate2':
                        {
                            True:{},
                            False:{literal4}
                        }
                    }
'''
class Clause:
    # initialize from a sentence string that contains no \n or spaces
    def __init__(self, sentence_str = None):
        self.clause_dict = {}
        self.hash_str = None
        if sentence_str:
            global num_vars_seen
            standard_var_assns = {}
            # p1&p2&~p3=>p4
            then_split = sentence_str.split('=>')
            # ['p1&p2&~p3', 'p4']
            all_literals = [then_split[-1]]
            # ['p4']
            if len(then_split) > 1:
                # ['p1&p2&~p3']; ['p4']
                all_literals = then_split[-2].split('&') + all_literals
                # ['p1', 'p2', '~p3', 'p4']
            for i, l in enumerate(all_literals):
                lit = Literal(l)
                # standardize variables
                for index, arg in enumerate(lit.arg_list):
                    # skip constants
                    if not arg.islower():
                        continue
                    current_assignment = standard_var_assns.get(arg)
                    if current_assignment is None:
                        new_assignment = standard_var_encode(num_vars_seen)
                        standard_var_assns[arg] = new_assignment
                        current_assignment = new_assignment
                        num_vars_seen += 1
                    lit.arg_list[index] = current_assignment
                # update string to standardiazed variables
                lit.literal_str = lit.to_string()
                # ~(A & B) == ~A V ~B
                # RHS of if doesn't need negation
                if i < (len(all_literals)-1):
                    lit.negate()
                if lit.predicate in self.clause_dict:
                    self.clause_dict[lit.predicate][lit.not_negated].add(lit)
                else:
                    self.clause_dict[lit.predicate] = {lit.not_negated:set([lit]),
                                                       not lit.not_negated:set()}
            # sentence_str needs to be converted into disjunctive clause
            self.hash_str = self.to_string()

    # returns a disjunctive clause string
    #   'p1|p2|~p3'
    # also returns a version where variables here are 'unstandardized' back to a,b,c etc.
    #   so Pred(aaa) and Pred(bbb) get hashed the same
    def to_string(self):
        var_counter = 0
        unstd_var_assns = {}
        hash_str_list = []
        for lit_by_tf in self.clause_dict.values():
            for lit_set in lit_by_tf.values():
                for lit in lit_set:
                    unstd_arg_list = []
                    for index, arg in enumerate(lit.arg_list):
                        if not arg.islower():
                            unstd_arg_list.append(arg)
                        else:
                            if arg not in unstd_var_assns:
                                # In our version of problem, variable has to be a single lower case letter
                                #   so it's guaranteed to be one of lower_case_letters
                                unstd_var_assns[arg] = lower_case_letters[var_counter]
                                var_counter += 1
                            unstd_arg_list.append(unstd_var_assns[arg])
                    hash_str_list.append('~'[lit.not_negated:] + lit.predicate + '(' + ','.join(unstd_arg_list) + ')')
        # order doesn't matter in disjunctive clause
        return '|'.join(sorted(hash_str_list))

    def __str__(self):
        return self.hash_str

    __repr__ = __str__

    def __eq__(self, other):
        return self.hash_str == other.hash_str

    # FIXME: logically equivalent sentences may be represented differently!!!
    def __hash__(self):
        return hash(self.hash_str)

    # returns a boolean indicating whether self contains complementary literals
    #   that is, whether self contains both Pred(a) and ~Pred(a)
    def check_tautology(self):
        for predicate, lit_by_tf in self.clause_dict.items():
            # Only need to check one direction
            for literal in lit_by_tf[True]:
                for possible_complement in lit_by_tf[False]:
                    if literal.arg_list == possible_complement.arg_list:
                        return True
        return False

    '''
    self and other are both clauses
    if resolvable returns a set of resolvent Clauses with substituted variables
        if empty set returned then contradiction found
    if not resolvable returns False
    '''
    def resolve_with_other(self, other):
        # given substitution dictionary theta, go into arg_list of all literals and substitute
        #   in_place but replaces lit_sets because literal hashes have been updated
        #   technically clause hash has also been updated but it is ONLY meant to be run on COPIES so no problem
        def substitute(clause_dict, theta):
            for predicate, lit_by_tf in clause_dict.items():
                for not_negated, lit_set in lit_by_tf.items():
                    new_lit_set = set()
                    for literal in lit_set:
                        new_literal = Literal()
                        new_literal.predicate = literal.predicate
                        new_literal.not_negated = literal.not_negated
                        new_literal.arg_list = [theta[arg] if arg in theta else arg for arg in literal.arg_list]
                        new_literal.literal_str = new_literal.to_string()
                        new_lit_set.add(new_literal)
                    clause_dict[predicate][not_negated] = new_lit_set

        # given 2 clause_dicts
        #   returns a new clause_dict with all non-repeating literals from both clause_dicts
        def combine(x, y):
            result = {}
            for predicate in (set(x.keys()) | set(y.keys())):
                x_pred_true = set()
                x_pred_false = set()
                if predicate in x:
                    x_pred_true = x[predicate][True]
                    x_pred_false = x[predicate][False]
                y_pred_true = set()
                y_pred_false = set()
                if predicate in y:
                    y_pred_true = y[predicate][True]
                    y_pred_false = y[predicate][False]
                pred_true = x_pred_true | y_pred_true
                pred_false = x_pred_false | y_pred_false
                # don't add predicate key if both are empty
                if pred_true or pred_false:
                    result[predicate] = {True:pred_true, False:pred_false}
            return result

        result = set()
        # if no unification has succeeded, the cannot resolve
        #   otherwise two clauses can resolve, even though resolvents returned may contain only empty clauses
        uni_dict_generated = False
        for predicate, lit_by_tf in self.clause_dict.items():
            for not_negated, lit_set in lit_by_tf.items():
                if predicate in other.clause_dict:
                    # can only resolve with same predicate and opposite negation
                    other_lit_set = other.clause_dict[predicate][not not_negated]
                    for self_literal in lit_set:
                        for other_literal in other_lit_set:
                            uni_dict = self_literal.unify_with_other(other_literal)
                            # uni_dict may be False or {}, or non_empty {}
                            #   False means unification failed between this pair of literals so continue and try another pair
                            #   {} means all arguments are constants and they match
                            if uni_dict == False:
                                continue
                            uni_dict_generated = True
                            self_clause_dict_copy = copy.deepcopy(self.clause_dict)
                            other_clause_dict_copy = copy.deepcopy(other.clause_dict)
                            # remove matched literals
                            self_clause_dict_copy[predicate][not_negated].remove(self_literal)
                            other_clause_dict_copy[predicate][not not_negated].remove(other_literal)
                            # substitute with unification results
                            substitute(self_clause_dict_copy, uni_dict)
                            substitute(other_clause_dict_copy, uni_dict)
                            # combine
                            resolvent = Clause()
                            resolvent.clause_dict = combine(self_clause_dict_copy, other_clause_dict_copy)
                            resolvent.hash_str = resolvent.to_string()
                            result.add(resolvent)
        return result if uni_dict_generated else False

'''
clause table: {
                 'predicate1':
                    {
                        True:{clause1,clause2},
                        False:{clause2}
                    },
                 'predicate2':
                    {
                        True:{},
                        False:{clause3,clause4}
                    }
                }
'''
class Solver:
    # given a Clause object
    #   fills clause_table
    def fill_clause_table(self, clause):
        for predicate, cls_by_tf in clause.clause_dict.items():
            not_negated_literals = clause.clause_dict[predicate][True]
            negated_literals = clause.clause_dict[predicate][False]
            if predicate in self.clause_table:
                # clause contains a not_negated literal Pred(X)
                if not_negated_literals:
                    self.clause_table[predicate][True].add(clause)
                # clause contains a negated literal ~Pred(X)
                if negated_literals:
                    self.clause_table[predicate][False].add(clause)
            else:
                self.clause_table[predicate] = {True:set([clause]) if not_negated_literals else set(),
                                                False:set([clause]) if negated_literals else set()}

    def add_clause(self, clause):
        self.fill_clause_table(clause)
        self.KB.add(clause)

    '''
    KB contains a set of clauses proven to have no contradiction
    clause_table contains newly derived clauses (and therefore might cause contradiction in the next iteration)
    Each iteration resolves all pairs in the Cartesian product between KB and clause_dict
    '''
    def __init__(self, infile='input.txt'):
        self.queries = []
        # for ease of finding compatible clauses
        self.clause_table = {}
        # keeps track of what we know, for ease when checking loop
        self.KB = set()
        with open(infile, 'r') as f:
            num_queries = int(f.readline().rstrip(' \n'))
            for _ in range(num_queries):
                sentence_str = f.readline().rstrip('\n').replace(' ', '')
                self.queries.append(Literal(sentence_str))
            num_sentences = int(f.readline().rstrip(' \n'))
            for _ in range(num_sentences):
                sentence_str = f.readline().rstrip('\n').replace(' ', '')
                self.KB.add(Clause(sentence_str))

    '''
    in each iteration, resolve all possible pairs of clauses and add resolvents to KB and clause_table
    if empty resolvent found at any time, terminates on True
    if no new clause found after resolving all pairs in an iteration, terminates on False
    '''
    def solve_query(self, query):
        solver_copy = copy.deepcopy(self)
        query_copy = copy.deepcopy(query)
        query_copy.negate()
        query_clause = Clause()
        query_clause.clause_dict = {query_copy.predicate:{query_copy.not_negated:set([query_copy]),
                                                          not query_copy.not_negated:set()}}
        query_clause.hash_str = query_copy.literal_str
        solver_copy.fill_clause_table(query_clause)
        while True:
            new_clauses = set()
            # FIXME: repeated resolution check???
            for clause1 in solver_copy.KB:
                for predicate, lit_by_tf in clause1.clause_dict.items():
                    if predicate in solver_copy.clause_table:
                        for not_negated, lit_set in lit_by_tf.items():
                            # if clause1 contains a predicate with certain negation
                            if lit_set:
                                # resolve with all clauses that also have this predicate and opposite negation
                                resolve_with = solver_copy.clause_table[predicate][not not_negated]
                                # if there are such clauses
                                if resolve_with:
                                    for clause2 in resolve_with:
                                        resolvents = clause1.resolve_with_other(clause2)
                                        # if not resolvable
                                        if resolvents == False:
                                            continue
                                        else:
                                            for r in resolvents:
                                                # don't consider tautologies
                                                if r.check_tautology():
                                                    continue
                                                # if resolvent isn't empty clause
                                                if r.clause_dict:
                                                    new_clauses.add(r)
                                                # if empty resolvent then contradiction found
                                                else:
                                                    return True
            # if no new clauses found after resolving all pairs in this iteration
            #   then we are in a loop
            if new_clauses.issubset(solver_copy.KB):
                return False
            for cls_by_tf in solver_copy.clause_table.values():
                for cls_set in cls_by_tf.values():
                    solver_copy.KB = solver_copy.KB | cls_set
            # add new clauses so the next iteration may use them
            solver_copy.clause_table = {}
            for c in new_clauses:
                solver_copy.fill_clause_table(c)

    def solve(self, outfile='output.txt'):
        result = []
        for q in self.queries:
            result.append(self.solve_query(q))
        with open(outfile, 'w') as f:
            for answer in result:
                f.write(str(answer).upper()+'\n')

if __name__ == "__main__":
    testCase = Solver()
    testCase.solve()
