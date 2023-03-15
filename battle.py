import argparse
import numpy as np
import math
import random
class Variable:
    '''Class for defining CSP variables.

      On initialization the variable object can be given a name and a
      list containing variable's domain of values. You can reset the
      variable's domain if you want to solve a similar problem where
      the domains have changed.

      To support CSP propagation, the class also maintains a current
      domain for the variable. Values pruned from the variable domain
      are removed from the current domain but not from the original
      domain. Values can be also restored.
    '''

    undoDict = dict()             #stores pruned values indexed by a
                                        #(variable,value) reason pair
    def __init__(self, name, domain):
        '''Create a variable object, specifying its name (a
        string) and domain of values.
        '''
        self._name = name                #text name for variable
        self._dom = list(domain)         #Make a copy of passed domain
        self._curdom = list(domain)      #using list
        self._value = None

    def __str__(self):
        return "Variable {}".format(self._name)

    def domain(self):
        '''return copy of variable domain'''
        return(list(self._dom))

    def domainSize(self):
        '''Return the size of the domain'''
        return(len(self.domain()))

    def resetDomain(self, newdomain):
        '''reset the domain of this variable'''
        self._dom = newdomain

    def getValue(self):
        return self._value

    def setValue(self, value):
        if value != None and not value in self._dom:
            print("Error: tried to assign value {} to variable {} that is not in {}'s domain".format(value,self._name,self._name))
        else:
            self._value = value    

    def unAssign(self):
        self.setValue(None)

    def isAssigned(self):
        return self.getValue() != None

    def name(self):
        return self._name

    def curDomain(self):
        '''return copy of variable current domain. But if variable is assigned
           return just its assigned value (this makes implementing hasSupport easier'''
        if self.isAssigned():
            return([self.getValue()])
        return(list(self._curdom))

    def curDomainSize(self):
        '''Return the size of the current domain'''
        if self.isAssigned():
            return(1)
        return(len(self._curdom))

    def inCurDomain(self, value):
        '''check if value is in current domain'''
        if self.isAssigned():
            return(value==self.getValue())
        return(value in self._curdom)

    def pruneValue(self, value, reasonVar, reasonVal):
        '''Remove value from current domain'''
        try:
            self._curdom.remove(value)
        except:
            print("Error: tried to prune value {} from variable {}'s domain, but value not present!".format(value, self._name))
        dkey = (reasonVar, reasonVal)
        if not dkey in Variable.undoDict:
            Variable.undoDict[dkey] = []
        Variable.undoDict[dkey].append((self, value))

    def restoreVal(self, value):
        self._curdom.append(value)

    def restoreCurDomain(self):
        self._curdom = self.domain()

    def reset(self):
        self.restoreCurDomain()
        self.unAssign()

    def dumpVar(self):
        print("Variable\"{}={}\": Dom = {}, CurDom = {}".format(self._name, self._value, self._dom, self._curdom))

    @staticmethod
    def clearUndoDict():
        undoDict = dict()

    @staticmethod
    def restoreValues(reasonVar, reasonVal):
        dkey = (reasonVar, reasonVal)
        if dkey in Variable.undoDict:
            for (var,val) in Variable.undoDict[dkey]:
                var.restoreVal(val)
            del Variable.undoDict[dkey]

class UnassignedVars:
    '''class for holding the unassigned variables of a CSP. We can extract
       from, re-initialize it, and return variables to it.  Object is
       initialized by passing a select_criteria (to determine the
       order variables are extracted) and the CSP object.

       select_criteria = ['random', 'fixed', 'mrv'] with
       'random' == select a random unassigned variable
       'fixed'  == follow the ordering of the CSP variables (i.e.,
                   csp.variables()[0] before csp.variables()[1]
       'mrv'    == select the variable with minimum values in its current domain
                   break ties by the ordering in the CSP variables.
    '''
    def __init__(self, select_criteria, csp):
        if select_criteria not in ['random', 'fixed', 'mrv']:
            pass #print "Error UnassignedVars given an illegal selection criteria {}. Must be one of 'random', 'stack', 'queue', or 'mrv'".format(select_criteria)
        # unassignedL = []
        # for var in csp.variables():
        #     if var._value == None:
        #         unassignedL.append(var)
        # self.unassigned = unassignedL
        self.unassigned = list(csp.variables())
        self.csp = csp
        self._select = select_criteria
        if select_criteria == 'fixed':
            #reverse unassigned list so that we can add and extract from the back
            self.unassigned.reverse()

    def extract(self):
        if not self.unassigned:
            print( "Warning, extracting from empty unassigned list")
            return None
        if self._select == 'random':
            i = random.randint(0,len(self.unassigned)-1)
            nxtvar = self.unassigned[i]
            self.unassigned[i] = self.unassigned[-1]
            self.unassigned.pop()
            return nxtvar
        if self._select == 'fixed':
            return self.unassigned.pop()
        if self._select == 'mrv':
            nxtvar = min(self.unassigned, key=lambda v: v.curDomainSize())
            self.unassigned.remove(nxtvar)
            return nxtvar

    def empty(self):
        return len(self.unassigned) == 0

    def insert(self, var):
        if not var in self.csp.variables():
            pass #print "Error, trying to insert variable {} in unassigned that is not in the CSP problem".format(var.name())
        else:
            self.unassigned.append(var)

#implement various types of constraints
class Constraint:
    '''Base class for defining constraints. Each constraint can check if
       it has been satisfied, so each type of constraint must be a
       different class. For example a constraint of notEquals(V1,V2)
       must be a different class from a constraint of
       greaterThan(V1,V2), as they must implement different checks of
       satisfaction.

       However one can define a class of general table constraints, as
       below, that can capture many different constraints.

       On initialization the constraint's name can be given as well as
       the constraint's scope. IMPORTANT, the scope is ordered! E.g.,
       the constraint greaterThan(V1,V2) is not the same as the
       contraint greaterThan(V2,V1).
    '''
    def __init__(self, name, scope):
        '''create a constraint object, specify the constraint name (a
        string) and its scope (an ORDERED list of variable
        objects).'''
        self._scope = list(scope)
        self._name = "baseClass_" + name  #override in subconstraint types!

    def scope(self):
        return list(self._scope)

    def arity(self):
        return len(self._scope)

    def numUnassigned(self):
        i = 0
        for var in self._scope:
            if not var.isAssigned():
                i += 1
        return i

    def unAssignedVars(self):
        return [var for var in self.scope() if not var.isAssigned()]

    # def check(self):
    #     util.raiseNotDefined()

    def name(self):
        return self._name

    def __str__(self):
        return "Cnstr_{}({})".format(self.name(), map(lambda var: var.name(), self.scope()))

    def printConstraint(self):
        print("Cons: {} Vars = {}".format(
            self.name(), [v.name() for v in self.scope()]))

def findvals(remainingVars, assignment, finalTestfn, partialTestfn=lambda x: True):
    '''Helper function for finding an assignment to the variables of a constraint
       that together with var=val satisfy the constraint. That is, this
       function looks for a supporing tuple.

       findvals uses recursion to build up a complete assignment, one value
       from every variable's current domain, along with var=val.

       It tries all ways of constructing such an assignment (using
       a recursive depth-first search).

       If partialTestfn is supplied, it will use this function to test
       all partial assignments---if the function returns False
       it will terminate trying to grow that assignment.

       It will test all full assignments to "allVars" using finalTestfn
       returning once it finds a full assignment that passes this test.

       returns True if it finds a suitable full assignment, False if none
       exist. (yes we are using an algorithm that is exactly like backtracking!)'''

    # print "==>findvars([",
    # for v in remainingVars: print v.name(), " ",
    # print "], [",
    # for x,y in assignment: print "({}={}) ".format(x.name(),y),
    # print ""

    #sort the variables call the internal version with the variables sorted
    remainingVars.sort(reverse=True, key=lambda v: v.curDomainSize())
    return findvals_(remainingVars, assignment, finalTestfn, partialTestfn)

def findvals_(remainingVars, assignment, finalTestfn, partialTestfn):
    '''findvals_ internal function with remainingVars sorted by the size of
       their current domain'''
    if len(remainingVars) == 0:
        return finalTestfn(assignment)
    var = remainingVars.pop()
    for val in var.curDomain():
        assignment.append((var, val))
        if partialTestfn(assignment):
            if findvals_(remainingVars, assignment, finalTestfn, partialTestfn):
                return True
        assignment.pop()   #(var,val) didn't work since we didn't do the return
    remainingVars.append(var)
    return False


class NValuesConstraint(Constraint):
    '''NValues constraint over a set of variables.  Among the variables in
       the constraint's scope the number that have been assigned
       values in the set 'required_values' is in the range
       [lower_bound, upper_bound] (lower_bound <= #of variables
       assigned 'required_value' <= upper_bound)

       For example, if we have 4 variables V1, V2, V3, V4, each with
       domain [1, 2, 3, 4], then the call
       NValuesConstraint('test_nvalues', [V1, V2, V3, V4], [1,4], 2,
       3) will only be satisfied by assignments such that at least 2 of
       the V1, V2, V3, V4 are assigned the value 1 or 4, and at most 3
       of them have been assigned the value 1 or 4.

    '''

    def __init__(self, name, scope, required_values, lower_bound, upper_bound):
        Constraint.__init__(self,name, scope)
        self._name = "NValues_" + name
        self._required = required_values # set = [1,4]
        self._lb = lower_bound # lower number of variables assigned to 1 or 4
        self._ub = upper_bound

    def check(self):
        """if among all variables that are assigned, whether the amount in set is within the range
        If no variables are assigned, then return True, since no rule is violated yet
        """
        # print(self.scope())
        assignments = []
        for v in self.scope():
            if v.isAssigned():
                assignments.append(v.getValue())
            else:
                return True
        rv_count = 0

        # print("Checking {} with assignments = {}".format(self.name(), assignments))

        for v in assignments:
            if v in self._required:
                rv_count += 1

        # print("rv_count = {} test = {}".format(rv_count, self._lb <= rv_count and self._ub >= rv_count))


        return self._lb <= rv_count and self._ub >= rv_count

    def hasSupport(self, var, val):
        '''check if var=val has an extension to an assignment of the
           other variable in the constraint that satisfies the constraint

           HINT: check the implementation of AllDiffConstraint.hasSupport
                 a similar approach is applicable here (but of course
                 there are other ways as well)
        '''
        if var not in self.scope():
            return True   #var=val has support on any constraint it does not participate in

        #define the test functions for findvals
        def valsOK(l):
            '''tests a list of assignments which are pairs (var,val)
               to see if they can satisfy this sum constraint'''
            rv_count = 0
            vals = [val for (var, val) in l]
            for v in vals:
                if v in self._required:
                    rv_count += 1
            least = rv_count + self.arity() - len(vals)
            most =  rv_count
            return self._lb <= least and self._ub >= most
        varsToAssign = self.scope()
        varsToAssign.remove(var)
        x = findvals(varsToAssign, [(var, val)], valsOK, valsOK)
        return x


#object for holding a constraint problem
class CSP:
    '''CSP class groups together a set of variables and a set of
       constraints to form a CSP problem. Provides a usesful place
       to put some other functions that depend on which variables
       and constraints are active'''

    def __init__(self, name, variables, constraints):
        '''create a CSP problem object passing it a name, a list of
           variable objects, and a list of constraint objects'''
        self._name = name
        self._variables = variables # eg. [ 36 Variable objects]
        self._constraints = constraints # eg. [Constraint objects...]

        #some sanity checks
        varsInCnst = set()
        for c in constraints:
            # print("c:",c)
            varsInCnst = varsInCnst.union(c.scope())
        for v in variables:
            if v not in varsInCnst:
                print("Warning: variable {} is not in any constraint of the CSP {}".format(v.name(), self.name()))
        for v in varsInCnst:
            if v not in variables:
                print("Error: variable {} appears in constraint but specified as one of the variables of the CSP {}".format(v.name(), self.name()))

        self.constraints_of = [[] for i in range(len(variables))]
        # print([var._name[-1] for var in variables] )
        for c in constraints:
            for v in c.scope():
                # print(v._name)
                i = variables.index(v)
                self.constraints_of[i].append(c)

    def name(self):
        return self._name

    def variables(self):
        return list(self._variables)

    def constraints(self):
        return list(self._constraints)

    def constraintsOf(self, var):
        '''return constraints with var in their scope'''
        try:
            i = self.variables().index(var)
            return list(self.constraints_of[i])
        except:
            print("Error: tried to find constraint of variable {} that isn't in this CSP {}".format(var, self.name()))

    def unAssignAllVars(self):
        '''unassign all variables'''
        for v in self.variables():
            v.unAssign()

    def check(self, solutions):
        '''each solution is a list of (var, value) pairs. Check to see
           if these satisfy all the constraints. Return list of
           erroneous solutions'''

        #save values to restore later
        current_values = [(var, var.getValue()) for var in self.variables()]
        errs = []

        # for s in solutions:
        s = solutions
        s_vars = [var for (var, val) in s]

        if len(s_vars) != len(self.variables()):
            errs.append([s, "Solution has incorrect number of variables in it"])
            # continue

        elif len(set(s_vars)) != len(self.variables()):
            errs.append([s, "Solution has duplicate variable assignments"])
            # continue

        elif set(s_vars) != set(self.variables()):
            errs.append([s, "Solution has incorrect variable in it"])
            # continue

        for (var, val) in s:
            var.setValue(val)

        for c in self.constraints():
            if not c.check():
                errs.append([s, "Solution does not satisfy constraint {}".format(c.name())])
                break

        for (var, val) in current_values:
            var.setValue(val)

        return errs
    
    def isComplete(self, assignment):
        """whether every var gets a value yet"""
        return len(self._variables) == len(assignment)
    
    def select_unassigned_variable(self, assignment):
        """
        
        """
        """ for forward checking pruning
        remaining_val = math.inf
        for var in self._variables:
            assigned_dom = 0
            for val in var._dom:
                if (var.getValue() == val):
                    assigned_dom += 1
            unassigned_dom = len(var._dom) - assigned_dom
            if unassigned_dom < remaining_val:
                remaining_val = unassigned_dom
                selected_var = var
        return selected_var
        """
        assigned_var = []
        for (var, val) in assignment:
            assigned_var.append(var)
        for v in self._variables:
            if v not in assigned_var:
                return v
        print("no successor")
        return 
    def order_domain_value(self, var, assignment):
        """Least-Constraining-Value Heuristic"""
        vals = []
        for val in var._dom:
            vals.append(val)
        print("vals", vals)
        return vals
    
    # def allSolutions(self):
    #     for var in self._variables:
    #         if (var.isAssigned() == False):
    #             return False
    #     return True

def BT2(unAssignedVars, csp, allSolutions, trace, filename):
    for var in unAssignedVars.unassigned:
            print([var._name[-1]])
    if unAssignedVars.empty():
        for var in csp._variables:
            print(var._name, "=", var._value)
        if allSolutions:
            print("Solution found!")
            output_to_file(filename, csp)
            return
        else:
            # print("Solution found!")
            return
    print("len:", len(unAssignedVars.unassigned))
    var = unAssignedVars.extract()
    for val in var._dom:
        # for var in csp._variable:
        #     print([var._name[-1]])
        var.setValue(val)
        constrainsOK = True
        for constraint in csp.constraintsOf(var):
            if constraint.numUnassigned() == 0:
                if not constraint.check():
                    constrainsOK = False
                    break
        if constrainsOK:
            BT(unAssignedVars, csp,  allSolutions, trace, filename)
    if var._name == "row: 0, col: 5, piece: 0":
        print("NO")
        var.setValue(None)
    unAssignedVars.insert(var)
    print("No Solution!")
    return


def BT(unAssignedVars, csp, allSolutions, trace, filename):
    '''Backtracking Search. unAssignedVars is the current set of
       unassigned variables.  csp is the csp problem, allSolutions is
       True if you want all solutionss trace if you want some tracing
       of variable assignments tried and constraints failed. Returns
       the set of solutions found.

      To handle finding 'allSolutions', at every stage we collect
      up the solutions returned by the recursive  calls, and
      then return a list of all of them.

      If we are only looking for one solution we stop trying
      further values of the variable currently being tried as
      soon as one of the recursive calls returns some solutions.
    '''
    if unAssignedVars.empty():
        if trace: pass #print "{} Solution Found".format(csp.name())
        soln = []
        for v in csp.variables():
            soln.append((v, v.getValue()))
        output_to_file(filename, soln)
        return [soln]  #each call returns a list of solutions found
    bt_search.nodesExplored += 1
    solns = []         #so far we have no solutions recursive calls
    nxtvar = unAssignedVars.extract()
    if trace: pass #print "==>Trying {}".format(nxtvar.name())
    for val in nxtvar.domain():
        if trace: pass #print "==> {} = {}".format(nxtvar.name(), val)
        nxtvar.setValue(val)
        constraintsOK = True
        for cnstr in csp.constraintsOf(nxtvar):
            if cnstr.numUnassigned() == 0:
                if not cnstr.check():
                    constraintsOK = False
                    if trace: pass #print "<==falsified constraint\n"
                    break
        if constraintsOK:
            new_solns = BT(unAssignedVars, csp, allSolutions, trace, filename)
            if new_solns:
                solns.extend(new_solns)
            if len(solns) > 0 and not allSolutions:
                break  #don't bother with other values of nxtvar
                       #as we found a soln.
    nxtvar.unAssign()
    unAssignedVars.insert(nxtvar)
    return solns

def bt_search(algo, csp, variableHeuristic, allSolutions, trace, filename):
    '''Main interface routine for calling different forms of backtracking search
       algorithm is one of ['BT', 'FC', 'GAC']
       csp is a CSP object specifying the csp problem to solve
       variableHeuristic is one of ['random', 'fixed', 'mrv']
       allSolutions True or False. True means we want to find all solutions.
       trace True of False. True means turn on tracing of the algorithm

       bt_search returns a list of solutions. Each solution is itself a list
       of pairs (var, value). Where var is a Variable object, and value is
       a value from its domain.
    '''
    varHeuristics = ['random', 'fixed', 'mrv']
    algorithms = ['BT', 'FC', 'GAC']

    #statistics
    bt_search.nodesExplored = 0

    if variableHeuristic not in varHeuristics:
        pass #print "Error. Unknown variable heursitics {}. Must be one of {}.".format(
            #variableHeuristic, varHeuristics)
    if algo not in algorithms:
        pass #print "Error. Unknown algorithm heursitics {}. Must be one of {}.".format(
            #algo, algorithms)

    uv = UnassignedVars(variableHeuristic,csp)
    Variable.clearUndoDict()
    for v in csp.variables():
        v.reset()
    if algo == 'BT':
         solutions = BT(uv, csp, allSolutions, trace, filename)
    # elif algo == 'FC':
    #     for cnstr in csp.constraints():
    #         if cnstr.arity() == 1:
    #             FCCheck(cnstr, None, None)  #FC with unary constraints at the root
    #     solutions = FC(uv, csp, allSolutions, trace)
    # elif algo == 'GAC':
    #     GacEnforce(csp.constraints(), csp, None, None) #GAC at the root
    #     solutions = GAC(uv, csp, allSolutions, trace)

    return solutions, bt_search.nodesExplored

def read_from_file(filename):
    """
    Load initial board from a given file.

    :param filename: The name of the given file.
    :type filename: str
    :return: A loaded board
    :rtype: Board
    """

    puzzle_file = open(filename, "r")

    line_index = 0
    pieces = []
    row_pieces = []
    for line in puzzle_file:
        if (line_index == 0):
                row_constraint = line[:-1]
        elif (line_index == 1):
                col_constraint = line[:-1]
        elif (line_index == 2):
                piece_constraint = line[:-1]
        else: 
            each_row_pieces = []
            for x, ch in enumerate(line):
                if ch != '\n':
                    string = "row: %d, col: %d, piece: %s"%(line_index-3,x,ch)
                    # each_row_pieces.append(Variable(string, ["0", ".", "S", "<", ">", "^", "v", "M"]))
                    # if ch == '0' or ch == 'S' or ch == '.': # found unknown piece
                        # print(line_index-3, x)
                    if ch == '0':
                        var = Variable(string, [".", "S"])
                    elif ch == ".":
                        var = Variable(string, ["."])
                    else:
                        var = Variable(string, ["S"])
                    pieces.append(var)
                    each_row_pieces.append(var)
                    # elif ch == 'S': # found submarine
                    #     pieces.append(Variable(string, ["0",".", "S", "<", ">", "^", "v", "M"]))
                    # elif ch == '.': # found water
                    #     pieces.append(Variable(string, ["0",".", "S", "<", ">", "^", "v", "M"]))

            row_pieces.append(each_row_pieces)
        line_index += 1
    # for p in pieces:
    #     print(p)
    puzzle_file.close()
    return pieces, row_pieces, col_constraint, row_constraint, piece_constraint

def row_col_pieces(row_pieces):
    col_pieces = []
    
    a = np.array(row_pieces, dtype=object)
    col_pieces = a.transpose()

    # names = []
    # for l in col_pieces:
    #     n = []
    #     for var in l:
    #         n.append(var._name[-1])
    #     names.append(n)
    # print(np.array(names))
    return col_pieces

def output_to_file(filename, sol):
    with open(filename,'r+') as file:
        file.truncate(0)
    f = open(filename, "a")
    # f.write("\n\nExploring:\n")
    rows = []
    count = 0
    for (var,val) in sol:
        if count == 6:
            count = 0
            f.write("\n")
            
        f.write(val) # ends with a new line
        # f.write("\n")
        count += 1
    f.write("\n")
    f.close()

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--inputfile",
        type=str,
        required=True,
        help="The input file that contains the puzzle."
    )
    parser.add_argument(
        "--outputfile",
        type=str,
        required=True,
        help="The output file that contains the solution."
    )
    
    args = parser.parse_args()

    variables, row_pieces, row_constraint, col_constraint, piece_constraint = read_from_file(args.inputfile)
    # print([var._name[-1] for var in variables] )
    # print(row_pieces)
    col_pieces = row_col_pieces(row_pieces)
    # print(col_pieces)
    all_constrains = []
    # Create column constraints
    for i in range(len(row_constraint)):
        ch = row_constraint[i]
        # print(ch,[var._name[-1] for var in row_pieces[i]] )
        all_constrains.append(NValuesConstraint('row_constraint idx: %d'%i, row_pieces[i], ["S"], int(ch), int(ch))) # "<", ">", "^", "v", "M"
    for i in range(len(col_constraint)):
        ch = col_constraint[i]
        # print(ch,[var._name[-1] for var in col_pieces[i]] )
        all_constrains.append(NValuesConstraint('col_constraint idx: %d'%i, col_pieces[i], ["S"], int(ch), int(ch)))
    csp = CSP("test", variables, all_constrains)

    result = bt_search("BT", csp, "fixed", allSolutions=True, trace=True, filename=args.outputfile)
    print(result)

    # c1 = all_constrains[0]
    # print(c1._name)
    # v = c1.scope()[0]
    # l = c1.hasSupport(v, "S")
    # print(l)