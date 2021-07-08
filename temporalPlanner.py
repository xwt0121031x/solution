from display import Displayable
from os import name
from searchProblem import Arc, Search_problem
from searchGeneric import AStarSearcher, Searcher
from cspConsistency import Con_solver, Search_with_AC_from_CSP, copy_with_assign, partition_domain, select
from cspProblem import CSP, Constraint
import sys

duration = dict()

def before():
    """t1 ends before t2 starts"""
    def before_(**kwargs):
        t = []
        d = []
        for k,v in kwargs.items():
            t.append(v)
            d.append(duration[k])
        return (t[0] + d[0] <= t[1])
    before_.__name__ = "before"
    return before_

def after():
    """ t1 starts after t2 ends"""
    def after_(**kwargs):
        t = []
        d = []
        for k,v in kwargs:
            t.append(v)
            d.append(duration[k])
        return t[0]>=t[1]+d[1]
    after_.__name__ = "after"
    return after_

def starts():
    """t1 and t2 start on the same day"""
    def starts_(**kwargs):
        t = []
        d = []
        for k,v in kwargs:
            t.append(v)
            d.append(duration[k])
        return t[0] == t[1]
    starts_.__name__ = "starts"
    return starts_

def ends():
    """t1 and t2 end on the same day"""
    def ends_(**kwargs):
        t = []
        d = []
        for k,v in kwargs:
            t.append(v)
            d.append(duration[k])
        return t[0]+d[0] == t[1]+d[1]
    ends_.__name__ = "ends"
    return ends_

def meets():
    """t2 starts the next day after t1 ends"""
    def meets_(**kwargs):
        t = []
        d = []
        for k,v in kwargs:
            t.append(v)
            d.append(duration[k])
        return t[1] == t[0] + d[0] + 1
    meets_.__name__ = "meets"
    return meets_

def overlaps():
    """
    t2 starts after t1 starts and not 
    after t1 ends, and ends after t1 ends
    """
    def overlaps_(**kwargs):
        t = []
        d = []
        for k,v in kwargs:
            t.append(v)
            d.append(duration[k])
        return  t[0]+d[0]>t[1]>t[0] and t[1] + d[1] > t[0] + d[0]
    overlaps_.__name__ = "overlaps"
    return overlaps_ 

def during():
    """
    t1 starts after t2 starts and ends before t2 ends
    """
    def during_(**kwargs):
        t = []
        d = []
        for k,v in kwargs:
            t.append(v)
            d.append(duration[k])
        return  t[0]+d[0]>t[1]>t[0] and t[1] + d[1] > t[0] + d[0]   
    during_.__name__ = "during"
    return during_

def equals():
    """
    t1 and t2 must be over the same interval
    """
    def equals_(**kwargs):
        t = []
        d = []
        for k,v in kwargs:
            t.append(v)
            d.append(duration[k])
        return  t[0]==t[1] and d[0]==d[1] 
    equals_.__name__ = "equals"
    return equals_

def starts_before(d):
    """
    t starts on or before d
    """
    def starts_before_(**kwargs):
        t = []
        d = []
        for k,v in kwargs:
            t.append(v)
            d.append(duration[k])
        return t[0] <= d 
    starts_before_.__name__ = "starts_before"
    return starts_before_

def starts_after(d):
    """
    t starts on or after d
    """
    def starts_after_(**kwargs):
        t = []
        d = []
        for k,v in kwargs:
            t.append(v)
            d.append(duration[k])
        return t[0] >= d 
    starts_after_.__name__ = "starts_after"
    return starts_after_

def ends_before(d):
    """
    t ends on or before d
    """
    def ends_before_(**kwargs):
        t = []
        d = []
        for k,v in kwargs:
            t.append(v)
            d.append(duration[k])
        return t[0]+d[0] <= d 
    ends_before_.__name__ = "ends_before"
    return ends_before_

def ends_after(d):
    """
    t ends on or after d
    """
    def ends_after_(**kwargs):
        t = []
        d = []
        for k,v in kwargs:
            t.append(v)
            d.append(duration[k])
        return t[0] + d[0] >= d 
    ends_after_.__name__ = "ends_after"
    return ends_after_

def starts_in(d1, d2):
    """
    t starts in the range [d1,d2]
    """
    def starts_in_(**kwargs):
        t = []
        d = []
        for k,v in kwargs:
            t.append(v)
            d.append(duration[k])
        return  d1 <= t[0] <= d2
    starts_in_.__name__ = "starts_in"
    return starts_in_

def ends_in(d1, d2):
    """
    t ends in the range [d1,d2]
    """
    def ends_in_(**kwargs):
        t = []
        d = []
        for k,v in kwargs:
            t.append(v)
            d.append(duration[k])
        return  d1 <= t[0]+d[0] <= d2 
    ends_in_.__name__ = "ends_in"
    return ends_in_

def between(d1, d2):
    """
    t starts and finishes in the range [d1,d2]
    """
    def between_(**kwargs):
        t = []
        d = []
        for k,v in kwargs:
            t.append(v)
            d.append(duration[k])
        return d1 <= t[0] <= d2 and t[0] + d[0] <= d2
    between_.__name__ = "between"
    return between_


class MyConstraint(Constraint):
    """A Constraint consists of
    * scope: a tuple of variables
    * condition: a function that can applied to a tuple of values
    * string: a string for printing the constraints. All of the strings must be unique.
    for the variables
    """
    def __init__(self, scope, condition, string):
        super().__init__(scope, condition, string=string)

    def holds(self,assignment):
        return self.condition(**{k:assignment[k] for k in self.scope})



class MyCSP(CSP):

    def __init__(self, domains, constraints, duration, positions = None):
        super().__init__(domains, constraints, positions=positions)
        # dict of tasks duration
        self.duration = duration

    def cost(self,assignment) :
        ret = 0
        if self.consistent(assignment):
            for var, val in assignment:
                if val is None:
                    ret += min(self.domains[var]) + self.duration[var] - 1
                else:
                    ret += val + self.duration[var] - 1
        return ret

class Search_with_AC_from_cost_CSP(Search_with_AC_from_CSP):

    def __init__(self, csp):
        super().__init__(csp)
        self.duration = csp.duration

    # the heuristic function(use A* Searcher)
    def heuristic(self,node):
        """
        Gives the heuristic value of node n.
        """
        ret = 0
        for k, v in node.items():
            ret += min(v) + self.duration[k] - 1
            pass
        return ret


class MySearcher(AStarSearcher):

    def __init__(self, problem):
        super().__init__(problem)

    def add_to_frontier(self, path):
        """add path to the frontier with the appropriate cost"""
        value = self.problem.heuristic(path.end())
        self.frontier.add(path,value)


class Loader():
    def __init__(self, path):
        self.path = path

    def get_file_content(self):
        f = open(self.path, 'r')
        content = f.readlines() # read() -> readlines()
        f.close()
        return content

class DataLoader(Loader):

    def get_line_list(self):
        lines = list(self.get_file_content())
        LineList = []
        for line in lines: 
           LineList.append(line.replace('\n', '').split(' '))
        return LineList

    def norm(self):
        lineList = self.get_line_list()
        constraints = []
        domains = {}
        for line in lineList:
            if line[0] == '#':
                continue
            elif line[0] == 'task':
                duration[line[1]] = int(line[2])
                domains[line[1]] = [ i for i in range(0, 100) ]
            elif line[0] == 'constraint':
                if line[2] == 'before':
                    constraints.append(MyConstraint([line[1], line[3]], before(), line[1] + ' before ' + line[3]) )
                elif line[2] == 'after':
                    constraints.append(MyConstraint([line[1], line[3]], after(), line[1] + ' after ' + line[3]) )
                elif line[2] == 'starts':
                    constraints.append(MyConstraint([line[1], line[3]], starts(), line[1] + ' starts ' + line[3]) )
                elif line[2] == 'ends':
                    constraints.append(MyConstraint([line[1], line[3]], ends(), line[1] + ' ends ' + line[3]) )
                elif line[2] == 'meets':
                    constraints.append(MyConstraint([line[1], line[3]], meets(), line[1] + ' meets ' + line[3]) )
                elif line[2] == 'overlaps':
                    constraints.append(MyConstraint([line[1], line[3]], overlaps(), line[1] + ' overlaps ' + line[3]) )
                elif line[2] == 'during':
                    constraints.append(MyConstraint([line[1], line[3]], during(), line[1] + ' during ' + line[3]) )
                elif line[2] == 'equals':
                    constraints.append(MyConstraint([line[1], line[3]], equals(), line[1] + ' equals ' + line[3]) )

            elif line[0] == 'domain':
                if line[2] == 'starts-after':
                    domains[line[1]] = list(filter(lambda x:x >= int(line[3]), domains[line[1]]))
                elif line[2] == 'starts-before':
                    domains[line[1]] = list(filter(lambda x:x <= int(line[3]), domains[line[1]]))
                elif line[2] == 'ends-before':
                    domains[line[1]] = list(filter(lambda x:x <= int(line[3]), domains[line[1]]))
                    
        return (duration, constraints, domains)


if __name__ == "__main__":
    path = sys.path[0] + '\\' + sys.argv[1]
    duration, constraints, domains = DataLoader(path).norm()
    csp = MyCSP(domains, constraints, duration)
    a = Search_with_AC_from_cost_CSP(csp)
    b = MySearcher(a)
    path1 = b.search()
    result = path1.end()
    final_cost = 0
    for k in result.keys():
        start_day = list(result[k])[0]
        print(k + ':' + str(start_day) )
        final_cost += start_day + duration[k] - 1
    print('cost:' + str(final_cost),end="")
