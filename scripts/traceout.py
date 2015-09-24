#!/usr/bin/python
"""
Parses debug output from SpecSFS
"""

import argparse
import collections

def is_special(val):
    """
    Determines if the id is special (it can't be offset'd)
    """
    return val < 7

class StoreVisit(object):
    """
    Represents a visit to a store node in the DUG
    """
    def __init__(self, node_id, rep, src, src_pts, dest, dest_pts, in_, in_end,
            out, out_end):
        self._id = node_id
        self._rep = rep
        self._src = src
        self._src_pts = src_pts
        self._dest = dest
        self._dest_pts = dest_pts
        self._in = in_
        self._in_end = in_end
        self._out = out
        self._out_end = out_end

    def __str__(self):
        ret = "store node: " + str(self._id) + "\n"
        ret += "  rep: " + str(self._rep) + "\n"
        ret += "  src: " + str(self._src) + " : " + str(self._src_pts) + "\n"
        ret += "  dest: " + str(self._dest) + " : " + str(self._dest_pts) + "\n"
        ret += "  in: " + str(self._in) + "\n"
        ret += "  in_end: " + str(self._in_end) + "\n"
        ret += "  out: " + str(self._out) + "\n"
        ret += "  out_end: " + str(self._out_end) + "\n"
        return ret

    def get_modified_taken(self):
        """
        Returns a list of address taken variables modified by visiting this node
        """
        ret = list()

        # Find the intersection of the two sets
        for in_val in self._dest_pts:
            start_set = self._out[in_val]
            end_set = self._out_end[in_val]

            diff_set = end_set.difference(start_set)

            # I something is changed
            if diff_set:
                ret.append(in_val)

        return ret

    def get_modified_top(self):
        """
        Returns a list of top level variables modified by visiting this node
        """
        # We modify no top level variables
        return list()

    def get_modified(self):
        """
        Returns a list of modified variables list contains tuples(addr_taken, id)
        """
        return [(True, x) for x in self.get_modified_taken()]

    # Check to see where the id_in_set came from
    def origin_of(self, addr_taken, pred_set, id_in_set):
        """
        Returns the tuple to identify the origin of the value requested, or none
        """
        assert pred_set
        assert addr_taken
        ret = None

        # If this came from an in set, then we return an addr_taken response
        #diff_set = self._in_end[pred_set] & self._in[pred_set]
        # There is a different node that changes it... we can ignore it
        #if id_in_set in diff_set:
        #    return None

        for in_val in self._dest_pts:
            start_set = self._out[in_val]
            end_set = self._out_end[in_val]
            in_set = self._in[in_val]

            diff_set = end_set.difference(start_set)

            # The id also shouldn't be in the in set
            diff_set = diff_set.difference(in_set)

            if id_in_set in diff_set:
                return (False, self._src)

        return ret

    def generate_ids(self, id_set):
        """
        Creates the id set for the node
        """
        id_set.add(self._rep)
        id_set.add(self._src)
        id_set.add(self._dest)

class LoadVisit(object):
    """
    Represents a visit to a load in the DUG
    """
    def __init__(self, node_id, rep, src, src_pts, dest, dest_pts, dest_pts_end,
            in_):
        self._id = node_id
        self._rep = rep
        self._src = src
        self._src_pts = src_pts
        self._dest = dest
        self._dest_pts = dest_pts
        self._dest_pts_end = dest_pts_end
        self._in = in_

    def __str__(self):
        ret = "load node: " + str(self._id) + "\n"
        ret += "  rep: " + str(self._rep) + "\n"
        ret += "  src: " + str(self._src) + " : " + str(self._src_pts) + "\n"
        ret += "  dest: " + str(self._dest) + " : " + str(self._dest_pts) + "\n"
        ret += "  dest_end: " + str(self._dest) + " : " + str(self._dest_pts_end) + "\n"
        ret += "  in: " + str(self._in) + "\n"
        return ret

    def get_modified_taken(self):
        """
        Returns a list of address taken variables modified by visiting this node
        """
        return list()

    def get_modified_top(self):
        """
        Returns a list of top level variables modified by visiting this node
        """
        # We modify no top level variables
        ret = list()

        start_set = self._dest_pts
        end_set = self._dest_pts_end

        diff_set = end_set.difference(start_set)

        if diff_set:
            ret.append(self._dest)

        return ret

    def get_modified(self):
        """
        Returns a list of modified variables list contains tuples(addr_taken, id)
        """
        return [(False, x) for x in self.get_modified_top()]

    # Check to see where the id_in_set came from
    def origin_of(self, addr_taken, pred_set, id_in_set):
        """
        Returns the tuple to identify the origin of the value requested, or none
        """
        assert not addr_taken
        assert pred_set == self._dest

        # If this came from an in set, then we return an addr_taken response
        for start_val in self._src_pts:
            in_set = self._in[start_val]
            dest_set = self._dest_pts

            if id_in_set not in dest_set and id_in_set in in_set:
                return (True, start_val)

        return None

    def generate_ids(self, id_set):
        """
        Creates the id set for the node
        """
        id_set.add(self._rep)
        id_set.add(self._src)
        id_set.add(self._dest)

class CopyVisit(object):
    """
    Represents a visit to a copy in the DUG
    """
    def __init__(self, node_id, rep, src, src_pts, dest, dest_pts, dest_pts_end,
            offset):
        self._id = node_id
        self._rep = rep
        self._src = src
        self._src_pts = src_pts
        self._dest = dest
        self._dest_pts = dest_pts
        self._dest_pts_end = dest_pts_end
        self._offset = offset

    def __str__(self):
        ret = "copy node: " + str(self._id) + "\n"
        ret += "  rep: " + str(self._rep) + "\n"
        ret += "  src: " + str(self._src) + " : " + str(self._src_pts) + "\n"
        ret += "  offset: " + str(self._offset) + "\n"
        ret += "  dest: " + str(self._dest) + " : " + str(self._dest_pts) + "\n"
        ret += "  dest_end: " + str(self._dest) + " : " + str(self._dest_pts_end) + "\n"
        return ret

    def get_modified_taken(self):
        """
        Returns a list of address taken variables modified by visiting this node
        """
        return list()

    def get_modified_top(self):
        """
        Returns a list of top level variables modified by visiting this node
        """
        # We modify no top level variables
        ret = list()

        start_set = self._dest_pts
        end_set = self._dest_pts_end

        diff_set = end_set.difference(start_set)

        if diff_set:
            ret.append(self._dest)

        return ret

    def get_modified(self):
        """
        Returns a list of modified variables list contains tuples(addr_taken, id)
        """
        return [(False, x) for x in self.get_modified_top()]

    # Check to see where the id_in_set came from
    def origin_of(self, addr_taken, pred_set, id_in_set):
        """
        Returns the tuple to identify the origin of the value requested, or none
        """
        assert not addr_taken
        assert self._dest == pred_set

        offset = self._offset

        # If this came from an in set, then we return an addr_taken response
        dest_pts = self._dest_pts
        for start_val in self._src_pts:
            if is_special(start_val):
                loffs = 0
            else:
                loffs = offset

            target_val = start_val + loffs
            # Need to somehow note the origin changed...
            if target_val == id_in_set:
                if target_val not in dest_pts:
                    return (False, self._src)

        return None

    def generate_ids(self, id_set):
        """
        Creates the id set for the node
        """
        id_set.add(self._rep)
        id_set.add(self._src)
        id_set.add(self._dest)

class AddressOfVisit(object):
    """
    Represents a visit to an addressof in the DUG
    """
    def __init__(self, node_id, rep, src, dest, dest_pts,
            offset, dest_pts_end):
        self._id = node_id
        self._rep = rep
        self._src = src
        self._dest = dest
        self._dest_pts = dest_pts
        self._dest_pts_end = dest_pts_end
        self._offset = offset

    def __str__(self):
        ret = "addressof node: " + str(self._id) + "\n"
        ret += "  rep: " + str(self._rep) + "\n"
        ret += "  src: " + str(self._src) + "\n"
        ret += "  dest: " + str(self._dest) + " : " + str(self._dest_pts) + "\n"
        ret += "  dest_end: " + str(self._dest) + " : " + str(self._dest_pts_end) + "\n"
        ret += "  offset: " + str(self._offset) + "\n"
        return ret

    def get_modified_taken(self):
        """
        Returns a list of address taken variables modified by visiting this node
        """
        return list()

    def get_modified_top(self):
        """
        Returns a list of top level variables modified by visiting this node
        """
        # We modify no top level variables
        ret = list()

        start_set = self._dest_pts
        end_set = self._dest_pts_end

        diff_set = end_set.difference(start_set)

        if diff_set:
            ret.append(self._dest)

        return ret

    def get_modified(self):
        """
        Returns a list of modified variables list contains tuples(addr_taken, id)
        """
        return [(False, x) for x in self.get_modified_top()]

    # Check to see where the id_in_set came from
    def origin_of(self, addr_taken, pred_set, id_in_set):
        """
        Returns the tuple to identify the origin of the value requested, or none
        """
        assert not addr_taken

        if id_in_set == self._src and pred_set == self._dest:
            return (False, self._src)

        return None

    def generate_ids(self, id_set):
        """
        Creates the id set for the node
        """
        id_set.add(self._rep)
        id_set.add(self._src)
        id_set.add(self._dest)

class PhiVisit(object):
    """
    Represents a visit to an phinode in the DUG
    """
    def __init__(self, node_id, rep, in_):
        self._id = node_id
        self._rep = rep
        self._in = in_

    def get_modified(self):
        """
        Returns a list of modified variables list contains tuples(addr_taken, id)
        """
        return list()

    # Check to see where the id_in_set came from
    def origin_of(self, addr_taken, pred_set, id_in_set):
        """
        Returns the tuple to identify the origin of the value requested, or none
        """
        assert not addr_taken
        assert pred_set == self._dest
        assert id_in_set == self._src
        return None

    def generate_ids(self, id_set):
        """
        Creates the id set for the node
        """
        id_set.add(self._rep)
        id_set.add(self._src)
        id_set.add(self._dest)

class GlobalInitVisit(object):
    """
    Represents a visit to an globalinit in the DUG
    """
    def __init__(self, node_id, rep, src, src_pts, dest, dest_pts,
            in_, in_end):
        self._id = node_id
        self._rep = rep
        self._src = src
        self._src_pts = src_pts
        self._dest = dest
        self._dest_pts = dest_pts
        self._in = in_
        self._in_end = in_end

    def __str__(self):
        ret = "global init node: " + str(self._id) + "\n"
        ret += "  rep: " + str(self._rep) + "\n"
        ret += "  src: " + str(self._src) + " : " + str(self._src_pts) + "\n"
        ret += "  dest: " + str(self._dest) + " : " + str(self._dest_pts) + "\n"
        ret += "  in: " + str(self._in) + "\n"
        ret += "  in_end: " + str(self._in_end) + "\n"
        return ret

    def get_modified_taken(self):
        """
        Returns a list of address taken variables modified by visiting this node
        """
        ret = list()

        # Find the intersection of the two sets
        for in_val in self._dest_pts:
            end_set = self._in_end[in_val]
            start_set = self._in[in_val]

            diff_set = end_set.difference(start_set)

            if diff_set:
                ret.append(in_val)

        return ret

    def get_modified_top(self):
        """
        Returns a list of top level variables modified by visiting this node
        """
        # We modify no top level variables
        return list()

    def get_modified(self):
        """
        Returns a list of modified variables list contains tuples(addr_taken, id)
        """
        return [(True, x) for x in self.get_modified_taken()]

    # Check to see where the id_in_set came from
    def origin_of(self, addr_taken, pred_set, id_in_set):
        """
        Returns the tuple to identify the origin of the value requested, or none
        """
        assert addr_taken
        ret = None

        # If this came from an in set, then we return an addr_taken response
        #diff_set = self._in_end[pred_set] & self._in[pred_set]
        # There is a different node that changes it... we can ignore it
        #if id_in_set in diff_set:
        #    return None

        for in_val in self._dest_pts:
            start_set = self._in[in_val]
            end_set = self._in_end[in_val]

            diff_set = end_set.difference(start_set)

            if id_in_set in diff_set:
                return (False, self._src)

        return ret

    def generate_ids(self, id_set):
        """
        Creates the id set for the node
        """
        id_set.add(self._rep)
        id_set.add(self._src)
        id_set.add(self._dest)

def parse_ptsset(word_list):
    """
    Parses a PtstoSet from the log
    """
    # format { val val val }
    ret = set()
    assert word_list[0] == "{" and word_list[-1] == "}"
    for word in word_list[1:-1]:
        ret.add(int(word))
    return ret

def parse_ptsgraph(word_list):
    """
    Parses a PtstoGraph from the log
    """
    # format ( id->{ val val val } id->{...} )
    ret = collections.defaultdict(set)

    assert word_list[0] == "(" and word_list[-1] == ")"

    cur_id = -1
    for word in word_list[1:-1]:
        if word[-1] == "{":
            cur_id = int(word[:-3])
        elif word != "}" and word != "},":
            assert cur_id != -1
            ret[cur_id].add(int(word))
    return ret

def parse_log(log_name):
    """
    Represents a visit to an globalinit in the DUG
    """
    taken_dict = collections.defaultdict(list)
    top_dict = collections.defaultdict(list)

    with open(log_name, "rb") as logfile:
        node_id = -1
        t = 0
        rep = 0
        dest = 0
        src = 0
        offset = 0
        dest_pts = None
        src_pts = None
        dest_pts_end = None
        in_ = None
        in_end = None
        out = None
        out_end = None
        have_solve = False
        for line in logfile:
            # Strip whitespace
            line = line.strip()
            # Okay, we gots us a line... for now, skip to solve
            if line == "SOLVE":
                have_solve = True
                continue

            if not have_solve:
                continue

            words = line.split()

            # node_id
            if words[0] == "n":
                if node_id != -1:
                    # Oh boy, do the node creation here...
                    # AddressOf
                    if t == 0:
                        visit = AddressOfVisit(node_id, rep, src,
                                dest, dest_pts, offset, dest_pts_end)
                    elif t == 1:
                        visit = StoreVisit(node_id, rep, src, src_pts,
                                dest, dest_pts,
                                in_, in_end, out, out_end)
                    elif t == 2:
                        visit = LoadVisit(node_id, rep, src, src_pts,
                                dest, dest_pts, dest_pts_end,
                                in_)
                    elif t == 3:
                        visit = GlobalInitVisit(node_id, rep, src, src_pts,
                                dest, dest_pts,
                                in_, in_end)
                    elif t == 4:
                        visit = CopyVisit(node_id, rep, src, src_pts,
                                dest, dest_pts, dest_pts_end,
                                offset)
                    elif t == 5:
                        visit = PhiVisit(node_id, rep, in_)
                    else:
                        assert False

                    modified_nodes = visit.get_modified()
                    for addr_taken, mod_id in modified_nodes:
                        if addr_taken:
                            taken_dict[mod_id].append(visit)
                        else:
                            top_dict[mod_id].append(visit)

                node_id = int(words[1])

            elif words[0] == "t":
                t = int(words[1])
            elif words[0] == "r":
                rep = int(words[1])
            elif words[0] == "s":
                src = int(words[1])
                if len(words) > 2:
                    src_pts = parse_ptsset(words[2:])
                else:
                    src_pts = set()
            elif words[0] == "d":
                dest = int(words[1])
                if len(words) > 2:
                    dest_pts = parse_ptsset(words[2:])
                else:
                    dest_pts = set()
            elif words[0] == "D":
                assert dest == int(words[1])
                if len(words) > 2:
                    dest_pts_end = parse_ptsset(words[2:])
                else:
                    dest_pts_end = set()
            elif words[0] == "f":
                offset = int(words[1])
            elif words[0] == "i":
                in_ = parse_ptsgraph(words[1:])
            elif words[0] == "I":
                in_end = parse_ptsgraph(words[1:])
            elif words[0] == "o":
                out = parse_ptsgraph(words[1:])
            elif words[0] == "O":
                out_end = parse_ptsgraph(words[1:])

    return (taken_dict, top_dict)

def trace_id(dep_taken, dep_top, id_in_set, set_in_question, is_addr_taken):
    """
    Traces the visit graph to find the origin of an id (id_in_set) within a
    PtstoSet (set_in_question), with the first hop potentially being addr_taken
    (is_addr_taken)
    """
    # So, heres what we do...
    # Find when id_in_set was added to set_in_question
    #   Taking into account if its addr_taken or top

    # the list of preds we're checking.. I think it will typically be
    # 1 element in size
    pred_id_list = [(is_addr_taken, x) for x in set_in_question]

    ret = list()

    visited = set()

    # While we have predecessors
    while pred_id_list:
        itr_pred_id_list = pred_id_list
        pred_id_list = list()

        # For each prior node
        for (addr_taken, pred) in itr_pred_id_list:
            # Find the potential candidate predecessors for this id
            if addr_taken:
                preds = dep_taken[pred]
            else:
                preds = dep_top[pred]

            # For each candidate, check if the are the origin of hte id in
            # the set
            for pred_visit in preds:
                if (pred_visit, addr_taken, pred, id_in_set) not in visited:
                    visited.add((pred_visit, addr_taken, pred, id_in_set))

                    origin = pred_visit.origin_of(addr_taken,
                            pred, id_in_set)


                    # If they know the set of origin, trace it next loop
                    if origin is not None:
                        ret.append(pred_visit)
                        pred_id_list.append(origin)

    return ret

def main(args):
    """
    Main operation of the tracer
    """
    # First, parse the file
    (dep_taken, dep_top) = parse_log(args.log_file)

    # Okay, we now have a dictionary...
    # Now, find the origin of id:
    id_in_set = int(args.id_in_set)
    set_in_question = [int(args.dest)]
    is_addr_taken = args.address_taken

    nodes = trace_id(dep_taken, dep_top, id_in_set, set_in_question, is_addr_taken)

    # If we should generate an id file, do it
    if args.generate_file:
        id_set = set()
        for node in nodes:
            node.generate_ids(id_set)

        with open(args.generate_file, "w") as gfile:
            for id_ in id_set:
                gfile.write(str(id_) + "\n")


        for node in reversed(nodes):
            print node

if __name__ == "__main__":
    parser = argparse.ArgumentParser("Analyze a SpecSFS execution, "+
            "print a trace")
    parser.add_argument("log_file", help="Log file from SpecSFS")
    parser.add_argument("id_in_set", help="Id to track")
    parser.add_argument("dest",
            help="Destination node of the first visit to trace")
    parser.add_argument("-a", "--address-taken", dest="address_taken",
            action="store_true")
    parser.add_argument("-g", "--generate-file", dest="generate_file",
            help="Causes traceout to print used ids into an output file")
    parser.add_argument("-l", "--load", dest="load_ids",
            help="Load the mapping of id to value string")
    main_args = parser.parse_args()
    main(main_args)

