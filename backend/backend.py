import xmltodict
import os
import sys, getopt
import random
from multiprocessing import Pool
from termcolor import colored
from tqdm import tqdm

RELATIONS = ["sch", "readpair", "writepair", "fencepair", "fenceanypair", "sthd", "rf", "sb", "sloc", "co", "fr"]
MDATA_REL = ["readpair", "writepair", "fencepair", "fenceanypair"]
EV = ["WrReq", "WrRsp", "RdReq", "RdRsp", "FnReq", "FnRsp", "FnReqAny",
      "FnRspAny", "CpuRead", "CpuWrite", "CpuFence"]
EV_F = ["WrReq", "WrRsp", "RdReq", "RdRsp", "FnReq", "FnRsp", "FnReqAny", "FnRspAny"]
EV_C = ["CpuRead", "CpuWrite", "CpuFence"]
FENCES = ["CpuFence", "FnReq", "FnRsp", "FnReqAny", "FnRspAny"]

INSTRUCTION_ENCODING = {"WrReq": "WR_REQ", "WrRsp": "WR_RSP", "RdReq": "RD_REQ", "RdRsp": "RD_RSP",
                        "FnReq": "FN_REQ", "FnRsp": "FN_RSP", "FnReqAny": "FN_REQANY", "FnRspAny": "FN_RSPANY"}
LOCATION_ENCODING = {0: "X_ADDR", 1: "Y_ADDR", 2: "Z_ADDR"}
CHANNEL_ENCODING = {0: "VL0", 1: "VH0", 2: "VH1", 100: "VA"}
#CHANNEL_ENCODING = {0: "VH0", 1: "VH1", 100: "VA"}
VARIABLES = {0: "x", 1: "y", 2: "z", 3: "s", 4: "t"}

NOT_REPRODUCIBLE_COLOR = "blue"
REPRODUCIBLE_COLOR = "green"
MESSAGE_COLOR = "yellow"


class Graph:
    def __init__(self, graph_dict=None):
        """ initializes a graph object
            If no dictionary or None is given,
            an empty dictionary will be used
            :param graph_dict: The graph to init with
        """
        if graph_dict is None:
            graph_dict = {}
        self.__graph_dict = graph_dict

    def vertices(self):
        """ returns the vertices of a graph """
        return list(self.__graph_dict.keys())

    def get_outer_degree(self, vertex, edge_type):
        """
        For a vertex, get the number of "edge_type" coming out
        :param vertex: The vertex
        :param edge_type: The edge type
        :return:
        """
        degree = 0
        for neighbour in self.__graph_dict[vertex]:
            (_, e_type) = neighbour
            if e_type == edge_type:
                degree = degree + 1
        return degree

    def add_vertex(self, vertex):
        """ If the vertex "vertex" is not in
            self.__graph_dict, a key "vertex" with an empty
            list as a value is added to the dictionary.
            Otherwise nothing has to be done.
            :param vertex: The vertex to add
        """
        if vertex not in self.__graph_dict:
            self.__graph_dict[vertex] = []

    def get_edges(self, vertex):
        """
        Return all the edges that are coming from a vertex
        :param vertex: The vertex you want the get the edges from
        :return: The list of edges
        """
        return self.__graph_dict[vertex]

    def add_edge(self, edge):
        """ Assumes that edge is of type set, tuple or list;
            between two vertices can be multiple edges!
        """
        (vertex1, vertex2, edge_type) = tuple(edge)
        if vertex1 in self.__graph_dict:
            self.__graph_dict[vertex1].append((vertex2, edge_type))
        else:
            self.__graph_dict[vertex1] = [vertex2]

    def get_first_node(self, node, edge_type):
        """
        Get the first node that has a "edge_type" pointing towards "node"
        :param node: The node
        :param edge_type: type of edge
        :return:
        """

        for vertex in self.__graph_dict:
            for edge in self.__graph_dict[vertex]:
                (v, e_type) = edge
                if (e_type == edge_type) and (v == node):
                    return vertex

    def dfs(self, vertex, visited, field, component, edge_type):
        """
        Depth first search of the graph
        :param vertex: The vertex to be visited
        :param visited: The dict of visited notes
        :param field: Where to store the component number
        :param component: The component you are part of
        :param edge_type: The type of edges you are working on
        :return:
        """

        # Mark the current vertex as visited
        visited[vertex] = True

        # Store the vertex to list
        field[vertex] = component

        # Repeat for all vertices adjacent
        # to this vertex v
        for edge in self.__graph_dict[vertex]:
            (v, e_type) = edge
            if e_type in edge_type:
                if not visited[v]:
                    self.dfs(v, visited, field, component, edge_type)

    def __str__(self):
        res = "Graph structure:\n "
        for ver in self.__graph_dict:
            res += "\tVertex " + str(ver) + ": "
            for edge in self.__graph_dict[ver]:
                res += "\t\t" + str(edge) + " " + "\n"
        return res


class Trace:
    """
    Holds all the information about a trace
    """

    def __init__(self, filename=None):
        self._xml = None
        self.graph = None
        self.filename = filename

        self._clear_data()

    def _clear_data(self):
        """
        Clear all the fields for a new execution
        :return:
        """

        self.graph = Graph()
        self.labels = {}
        self.write_value = {}

        self.threads = {}
        self.location = {}
        self.mdata = {}
        self.channel = {}
        self.sequence = {}

        self.fpga_threads = []
        self.cpu_threads = []

    @property
    def get_number_events(self):
        return len(self.sequence)

    @property
    def has_fences(self):
        fence_present = False
        for event in self.labels:
            if self.labels[event] in FENCES:
                fence_present = True
        return fence_present

    @property
    def get_number_threads(self):
        return max(self.threads.values()) + 1

    @property
    def get_number_locations(self):
        return max(self.location.values())

    @property
    def get_number_channels(self):
        temp_dict = {key:val for key, val in self.channel.items() if val != 100}

        return max(temp_dict.values())

    @property
    def get_number_cpu_threads(self):
        cpu_threads = 0
        for thread in range(self.get_number_threads):
            for event in self.threads:
                if (self.labels[event] in EV_C) and (self.threads[event] == thread):
                    cpu_threads += 1
                    break
        return cpu_threads

    @property
    def get_number_fpga_threads(self):
        fpga_threads = 0
        for thread in range(self.get_number_threads):
            for event in self.threads:
                if (self.labels[event] in EV_F) and (self.threads[event] == thread):
                    fpga_threads += 1
                    break
        return fpga_threads

    def get_thread_operations(self, thread):
        """
        Get the number of operations of a thread
        :param thread: The thread
        :return: The number of operations
        """
        operations = 0
        for event in self.threads:
            if self.threads[event] == thread:
                operations = operations + 1
        return operations

    def _set_operation_order(self):
        """
        Fill in the _sequence field
        :return: None
        """
        for event in self.graph.vertices():
            thread = self.threads[event]
            thread_operations = self.get_thread_operations(thread)
            self.sequence[event] = thread_operations - self.graph.get_outer_degree(event, "sb") - 1

    def _set_thread_type(self):
        """
        Fill in the self._cpu_threads and self_fpga_threads
        :return: None
        """
        for event in self.threads:
            if (self.labels[event] in EV_C) and not (event in self.cpu_threads):
                self.cpu_threads.append(event)
            if (self.labels[event] in EV_F) and not (event in self.fpga_threads):
                self.fpga_threads.append(event)

    def _connected_components(self, field, edge_type, allowed_labels):
        """
        :param field: Where to store the component number
        :param edge_type: The edges to fallow
        :param allowed_labels: Only jump to noted that have this label
        :return: None
        """
        visited = {}
        component = 0
        for vertex in self.graph.vertices():
            if self.labels[vertex] in allowed_labels:
                visited[vertex] = False
        for vertex in self.graph.vertices():
            if self.labels[vertex] in allowed_labels:
                if not visited[vertex]:
                    self.graph.dfs(vertex, visited, field, component, edge_type)
                    component = component + 1

    def _process_mdata(self):
        """
        Fill in the self._mdata field
        :return:
        """
        self._connected_components(self.mdata, MDATA_REL, EV_F)

        # pad the _mdata
        try:
            max_mdata = max(self.mdata.values())
        except ValueError:
            max_mdata = -1
        for event in self.labels:
            if event not in self.mdata:
                max_mdata += 1
                self.mdata[event] = max_mdata

    def _process_graph(self):
        """
        Process the self._xml and create the self._graph data
        :return:
        """

        # Add the events as nodes to the graph
        for field in self._xml['alloy']['instance']['field']:
            if field['@label'] == 'EV' and 'tuple' in field:
                if isinstance(field['tuple'], dict):
                    self.graph.add_vertex(field['tuple']['atom'][1]['@label'])
                else:
                    for t in field['tuple']:
                        self.graph.add_vertex(t['atom'][1]['@label'])

        # Add the relations as edges to the graph
        for field in self._xml['alloy']['instance']['field']:
            if field['@label'] in RELATIONS and 'tuple' in field:
                if isinstance(field['tuple'], dict):
                    vertex1 = field['tuple']['atom'][1]['@label']
                    vertex2 = field['tuple']['atom'][2]['@label']
                    edge = (vertex1, vertex2, field['@label'])
                    self.graph.add_edge(edge)
                    if field['@label'] in MDATA_REL:
                        backwards_edge = (vertex2, vertex1, field['@label'])
                        self.graph.add_edge(backwards_edge)
                else:
                    for t in field['tuple']:
                        vertex1 = t['atom'][1]['@label']
                        vertex2 = t['atom'][2]['@label']
                        edge = (vertex1, vertex2, field['@label'])
                        self.graph.add_edge(edge)
                        if field['@label'] in MDATA_REL:
                            backwards_edge = (vertex2, vertex1, field['@label'])
                            self.graph.add_edge(backwards_edge)

        value = 1
        register = 0
        # Add a label to each of the nodes
        for field in self._xml['alloy']['instance']['field']:
            if field['@label'] in EV and 'tuple' in field:
                if isinstance(field['tuple'], dict):
                    vertex = field['tuple']['atom'][1]['@label']
                    self.labels[vertex] = field['@label']
                    self.write_value[vertex] = 0
                    if self.labels[vertex] == "CpuWrite" or self.labels[vertex] == "WrReq":
                        self.write_value[vertex] = value
                        value += 1
                    if self.labels[vertex] == "CpuRead":
                        self.write_value[vertex] = register
                        register += 1
                else:
                    for t in field['tuple']:
                        vertex = t['atom'][1]['@label']
                        self.labels[vertex] = field['@label']
                        self.write_value[vertex] = 0
                        if self.labels[vertex] == "CpuWrite" or self.labels[vertex] == "WrReq":
                            self.write_value[vertex] = value
                            value += 1
                        if self.labels[vertex] == "CpuRead":
                            self.write_value[vertex] = register
                            register += 1

        self._connected_components(self.threads, "sthd", EV)
        self._connected_components(self.location, "sloc", ["CpuWrite", "CpuRead", "RdReq", "RdRsp", "WrReq", "WrRsp"])
        self._connected_components(self.channel, "sch", EV_F)

        # Add the special channel for FnReqAny
        for event in self.labels:
            if self.labels[event] in ["FnReqAny", "FnRspAny"]:
                self.channel[event] = 100

        self._set_operation_order()
        self._process_mdata()
        self._set_thread_type()

    def get_execution(self, filename):
        """
        Get the execution from the file with "number"
        :param filename: The file for thrace
        :return: True if was able to get the execution
        """
        self.filename = filename
        try:
            with open(filename) as fd:
                self._xml = xmltodict.parse(fd.read())
        except IOError:
            print("File was not processed")
            return False
        self._clear_data()
        self._process_graph()
        return True

    def __eq__(self, other):
        if self.get_number_events != other.get_number_events or self.get_number_threads != other.get_number_threads:
            return False

        event_matches = {}

        for event1 in self.sequence:
            found = False
            for event2 in other.sequence:
                if self.sequence[event1] == other.sequence[event2] and \
                        self.threads[event1] == other.threads[event2] and \
                        self.labels[event1] == other.labels[event2]:
                    event_matches[event1] = event2
                    found = True
            if not found:
                return False

        for event, event_pair in event_matches.items():
            edges = self.graph.get_edges(event)
            new_edges = []
            for edge in edges:
                (vertex, type) = edge
                new_edges.append((event_matches[vertex], type))
            new_edges = set(new_edges)

            edges_pair = set(other.graph.get_edges(event_pair))
            if new_edges != edges_pair:
                return False

        return True

    def __str__(self):
        res = str(self.graph)
        res += "\nlabels:\n "

        for k in self.labels:
            res += "\t" + str(k) + " " + self.labels[k] + "\n"

        return res


class TracesList:
    DIR = 'traces'

    def __init__(self):
        self.executions = []
        self.unique_executions = []
        self._files = [name for name in os.listdir(self.DIR) if os.path.isfile(os.path.join(self.DIR, name))]
        self._files.sort()

    @property
    def get_number_executions(self):
        return len(self.executions)

    def populate_list(self, maximum_traces=None, unique=True, shuffle=False):

        for file_nr, file in enumerate(self._files):
            ex = Trace()
            ex.get_execution(os.path.join(self.DIR, file))
            self.executions.append(ex)
            if maximum_traces:
                if file_nr > int(maximum_traces):
                    break

        print(str(self.get_number_executions) + " traces read")
        if unique:
            self.remove_duplicates()
        if shuffle:
            random.shuffle(self.executions)
            random.shuffle(self.unique_executions)

    @property
    def get_number_unique_executions(self):
        return len(self.unique_executions)

    def print_files(self):
        for file in self._files:
            print(file)

    def remove_duplicates(self):

        for i in range(len(self.executions)):
            unique = True
            for j in range(i + 1, len(self.executions)):
                if self.executions[i] == self.executions[j]:
                    unique = False
            if unique:
                self.unique_executions.append(self.executions[i])
        print(str(len(self.unique_executions)) + " unique traces")


class HardwareTests:
    """
    Contains the tests for the actual hardware
    """
    HARDWARE_TESTS_FOLDER = "litmus_tests"

    HARDWARE_CPU_THREADS = 4
    HARDWARE_FPGA_THREADS = 1

    def __init__(self, executions):

        self.executions = executions

        self.create_folder(self.HARDWARE_TESTS_FOLDER)

    @staticmethod
    def create_folder(path):
        try:
            os.mkdir(path)
        except OSError:
            pass
        else:
            print("Successfully created the directory %s " % path)

    def create_all_traces(self, remove_fences=False):

        software_executables = []

        for number, ex in enumerate(self.executions):
            if remove_fences and not ex.has_fences:
                continue
            if ex.get_number_cpu_threads > self.HARDWARE_CPU_THREADS or \
                    ex.get_number_fpga_threads > self.HARDWARE_FPGA_THREADS or \
                    ex.get_number_channels >= len(CHANNEL_ENCODING)-1 or \
                    ex.get_number_locations > len(LOCATION_ENCODING):
                continue

            software_executables.append(self.create_hardware_trace(number, ex))

        return software_executables

    def create_hardware_trace(self, number, ex):

        # Create folder structure
        test_name = "test_" + str(number)
        folder = self.HARDWARE_TESTS_FOLDER + "/test"
        self.create_folder(folder)
        folder_sw = folder + "/sw_" + str(number)
        self.create_folder(folder_sw)

        # Create the makefile
        makefile_sw = folder_sw + "/" + "Makefile"
        with open("template/sw/Makefile") as template:
            with open(makefile_sw, "w") as output:
                for line in template:
                    output.write(line.replace("<test_name>", test_name))

        # Create the .h file
        h_file = folder_sw + "/" + test_name + ".h"
        with open("template/sw/template.h") as template:
            with open(h_file, "w") as output:
                for line in template:
                    output.write(line.replace("<test_name>", test_name))

        # Create the .cpp file
        h_file = folder_sw + "/" + test_name + ".cpp"
        with open("template/sw/template.cpp") as template:
            with open(h_file, "w") as output:
                for line in template:
                    new_line = line.replace("<test_name>", test_name)
                    new_line = new_line.replace("<thread_declaration>", self._cpu_thread_generation(ex))
                    new_line = new_line.replace("<cpu_threads>", self._cpu_thread_control_generation(ex))
                    new_line = new_line.replace("<fpga_thread>", self._cpu_fpga_instruction(ex))
                    new_line = new_line.replace("<assert_test>", self._generate_assertions(ex))
                    output.write(new_line)

        return (folder_sw, test_name)

    def _generate_assertions(self, ex):

        code = "\t\t\t\t\tif( (\n"

        read_list =[]
        write_list = []

        for event in ex.labels:
            r_event = event
            if ex.labels[r_event] in ["WrRsp", "CpuWrite"] and not ex.graph.get_outer_degree(r_event, "co"):
                code += "                 (" + str(VARIABLES[ex.location[r_event]]) +"_buf[i*ELEM_LINE]"
                if ex.labels[r_event] == "WrRsp":
                    r_event = ex.graph.get_first_node(r_event, "writepair")
                code += " == " + str(ex.write_value[r_event]) + ") && \n "

        for event in ex.labels:
            if ex.labels[event] in ["CpuRead", "RdRsp"]:
                read_vertex = ex.graph.get_first_node(event, "rf")
                if ex.labels[event] == "CpuRead":
                    read_list.append("r" + str(ex.write_value[event]) + "[i]" )
                else:
                    read_list.append( "read_registers_buf[i*ELEM_LINE + " + str(ex.sequence[event]) + "]")
                if read_vertex:
                    if ex.labels[read_vertex] == "WrRsp":
                        read_vertex = ex.graph.get_first_node(read_vertex, "writepair")
                    write_list.append(str(ex.write_value[read_vertex]))
                else:
                    write_list.append("42")

        for i in range(len(read_list) - 1):
            code += "                 (" + read_list[i] + " == " + write_list[i] + ") &&\n"

        code += "                (" + read_list[-1] + " == " + write_list[-1] + ") \n"
        code += "                   ) \n                ) { \n"
        code += "\t valid_test = 0;\n"
        code += "}\n"

        return code

    def _cpu_fpga_instruction(self, ex):

        fpga_thread = None
        for event in ex.threads:
            if event in ex.fpga_threads:
                fpga_thread = ex.threads[event]

        fpga_thread_body = self._prepare_instruction_csr(ex, fpga_thread, 0)
        fpga_thread_body += self._prepare_instruction_csr(ex, fpga_thread, 1)
        fpga_thread_body += self._prepare_instruction_csr(ex, fpga_thread, 2)
        fpga_thread_body += self._prepare_instruction_csr(ex, fpga_thread, 3)

        return fpga_thread_body

    def _prepare_instruction_csr(self, ex, fpga_thread, offset):
        fpga_thread_body = "\t\twriteTestCSR(" + str(offset + 11) + ",\n"
        for i in range(0, 2):
            for event in ex.threads:
                if (ex.threads[event] == fpga_thread) and (ex.sequence[event] == i + 2*offset):

                    fpga_thread_body += "\t\t\t\t\t\t\t" + INSTRUCTION_ENCODING[ex.labels[event]].ljust(9)
                    fpga_thread_body += "<< " + str(i * 13).ljust(2) + "\t|" + "\t\t// Event " + str(
                        i + 2 * offset) + "\n"

                    try:
                        fpga_thread_body += "\t\t\t\t\t\t\t" + LOCATION_ENCODING[ex.location[event]].ljust(9)
                        fpga_thread_body += "<< " + str(i * 13 + 3).ljust(2) + "\t| \n"
                    except:
                        # Fences do not have a location
                        fpga_thread_body += "\t\t\t\t\t\t\t" + "0".ljust(9)
                        fpga_thread_body += "<< " + str(i * 13 + 3).ljust(2) + "\t| \n"


                    fpga_thread_body += "\t\t\t\t\t\t\t" + CHANNEL_ENCODING[ex.channel[event]].ljust(9)
                    fpga_thread_body += "<< " + str(i * 13 + 5).ljust(2) + "\t| \n"

                    fpga_thread_body += "\t\t\t\t\t\t\t" + str(ex.mdata[event]).ljust(9)
                    fpga_thread_body += "<< " + str(i * 13 + 7).ljust(2) + "\t|" + "\t\t// Mdata " + "\n"

                    try:
                        fpga_thread_body += "\t\t\t\t\t\t\t" + str(ex.write_value[event]).ljust(9)
                        fpga_thread_body += "<< " + str(i * 13 + 10).ljust(2) + "\t|" + "\t\t// Write value " + "\n"
                    except:
                        fpga_thread_body += "\t\t\t\t\t\t\t" + "0".ljust(9)
                        fpga_thread_body += "<< " + str(i * 13 + 10).ljust(2) + "\t|" + "\t\t// Write value " + "\n"

        fpga_thread_body += "\t\t\t\t\t\t\t0);\n"

        return fpga_thread_body

    def _cpu_thread_control_generation(self, ex):

        thread_body = ""

        for thread in range(0, ex.get_number_threads):
            for event in ex.threads:
                if (ex.threads[event] == thread) and (event in ex.cpu_threads):
                    thread_body += "\tstd::thread t" + str(thread) + " (thread" + str(thread)
                    thread_body += ", x_buf, y_buf, z_buf, repeat" + ");\n"
                    break

        thread_body += "\n"

        for thread in range(0, ex.get_number_threads):
            for event in ex.threads:
                if (ex.threads[event] == thread) and (event in ex.cpu_threads):
                    thread_body += "\tt" + str(thread) + ".join();\n "
                    break
        return thread_body

    def _prepare_cpu_thread_declaration(self, ex, thread):

        operations = ex.get_thread_operations(thread)

        thread_body = "void thread" + str(thread)
        thread_body += "(volatile uint64_t * x, volatile uint64_t * y, volatile uint64_t * z, uint64_t repeat) {\n"
        thread_body += "\tfor (int i=0; i < repeat; i++) {\n"
        for i in range(operations):
            for event in ex.threads:
                if (ex.threads[event] == thread) and (ex.sequence[event] == i):
                    if ex.labels[event] == "CpuWrite":
                        thread_body += "\t\t" + VARIABLES[ex.location[event]]
                        thread_body += "[i*ELEM_LINE] = " + str(ex.write_value[event]) + ";" + "\n"
                    if ex.labels[event] == "CpuRead":
                        thread_body += "\t\t" + "r" + str(ex.write_value[event]) + "[i]="
                        thread_body += VARIABLES[ex.location[event]] + "[i*ELEM_LINE];\n"
                    if ex.labels[event] == "CpuFence":
                        thread_body += "\t\t" + "std::atomic_thread_fence(std::memory_order_seq_cst);" + "\n"
        thread_body += "\t } \n } \n\n"

        return thread_body

    def _cpu_thread_generation(self, ex):

        thread_declaration = ""
        for thread in range(0, ex.get_number_threads):
            for event in ex.threads:
                if (ex.threads[event] == thread) and (event in ex.cpu_threads):
                    thread_declaration += self._prepare_cpu_thread_declaration(ex, thread)
                    break

        return thread_declaration


class CbmcTests:
    """
    Generates the H file and the CPP files for the CBMC test
    """
    CBMC_CPU_THREADS = 2
    CBMC_FPGA_THREADS = 1
    CBMC_VARIABLES = 5

    def __init__(self, executions):

        self._executions = None
        self.alloy_traces_h = None
        self.alloy_traces_c = None

        self._executions = executions

    @staticmethod
    def pretty_item(event, label, variable, write_value, mdata, channel):
        code = ""
        code += str(event).ljust(6)
        code += str(label).ljust(10)
        code += str(variable).ljust(6)
        code += str(write_value).ljust(6)
        code += str(mdata).ljust(6)
        code += str(channel).ljust(6)
        code += "\n"
        return code

    def pretty_print(self, execution):
        code = "/*\n"
        code += "Filename: " + execution.filename + "\n"

        for thread in range(execution.get_number_threads):
            code += "Thread " + str(thread) + "\n"
            code += "Label".ljust(6) + "Event".ljust(10) + "Loc".ljust(6) + "Val".ljust(6) + "Mdata".ljust(
                6) + "Channel".ljust(6)
            code += "\n"
            for operation in range(execution.get_thread_operations(thread)):
                for event in execution.labels:
                    if execution.threads[event] == thread and execution.sequence[event] == operation:
                        if execution.labels[event] == "WrReq":
                            code += self.pretty_item(event[-1],
                                                     execution.labels[event],
                                                     VARIABLES[execution.location[event]],
                                                     execution.write_value[event],
                                                     execution.mdata[event],
                                                     CHANNEL_ENCODING[execution.channel[event]])
                        if execution.labels[event] == "WrRsp":
                            code += self.pretty_item(event[-1],
                                                     execution.labels[event],
                                                     VARIABLES[execution.location[event]],
                                                     "",
                                                     execution.mdata[event],
                                                     CHANNEL_ENCODING[execution.channel[event]])
                        if execution.labels[event] == "FnReq":
                            code += self.pretty_item(event[-1],
                                                     execution.labels[event],
                                                     "",
                                                     "",
                                                     execution.mdata[event],
                                                     CHANNEL_ENCODING[execution.channel[event]])
                        if execution.labels[event] == "FnRsp":
                            code += self.pretty_item(event[-1],
                                                     execution.labels[event],
                                                     "",
                                                     "",
                                                     execution.mdata[event],
                                                     CHANNEL_ENCODING[execution.channel[event]])
                        if execution.labels[event] == "FnReqAny":
                            code += self.pretty_item(event[-1],
                                                     "FnReq",
                                                     "",
                                                     "",
                                                     execution.mdata[event],
                                                     CHANNEL_ENCODING[execution.channel[event]])
                        if execution.labels[event] == "FnRspAny":
                            code += self.pretty_item(event[-1],
                                                     "FnRsp",
                                                     "",
                                                     "",
                                                     execution.mdata[event],
                                                     CHANNEL_ENCODING[execution.channel[event]])
                        if execution.labels[event] == "RdReq":
                            code += self.pretty_item(event[-1],
                                                     execution.labels[event],
                                                     VARIABLES[execution.location[event]],
                                                     "",
                                                     execution.mdata[event],
                                                     CHANNEL_ENCODING[execution.channel[event]])
                        if execution.labels[event] == "RdRsp":
                            code += self.pretty_item(event[-1],
                                                     execution.labels[event],
                                                     VARIABLES[execution.location[event]],
                                                     "",
                                                     execution.mdata[event],
                                                     CHANNEL_ENCODING[execution.channel[event]])
                        if execution.labels[event] == "CpuRead":
                            code += self.pretty_item(event[-1],
                                                     execution.labels[event],
                                                     VARIABLES[execution.location[event]],
                                                     "",
                                                     "",
                                                     "")
                        if execution.labels[event] == "CpuWrite":
                            code += self.pretty_item(event[-1],
                                                     execution.labels[event],
                                                     VARIABLES[execution.location[event]],
                                                     execution.write_value[event],
                                                     "",
                                                     "")
                        if execution.labels[event] == "CpuFence":
                            code += self.pretty_item(event[-1],
                                                     execution.labels[event],
                                                     "",
                                                     "",
                                                     "",
                                                     "")
            code += "\n"

        read_list = []
        write_list = []
        for event in execution.labels:
            if execution.labels[event] in ["RdRsp", "CpuRead"]:
                read_vertex = execution.graph.get_first_node(event, "rf")
                read_list.append("read " + event[-1])
                if read_vertex:
                    write_list.append("write " + read_vertex[-1])
                else:
                    write_list.append("init value")

        code += "==============================================================\n"
        code += "Asserting that NOT all can be simultaneously true\n"
        for event in execution.labels:
            if execution.labels[event] in ["WrRsp", "CpuWrite"] and not execution.graph.get_outer_degree(event, "co"):
                code += "\tLast write at loc " + str(VARIABLES[execution.location[event]])
                code += " was event " + event[-1] + "\n"
        for i in range(len(read_list)):
            code += "\t" + read_list[i] + " == " + write_list[i] + "\n"

        code += "*/\n"

        return code

    def cbmc_trace(self, number, ex, fences_remove=False):

        nr_fences_removed = 0
        code = "void trace_" + str(number) + "(){\n\n"

        for event in ex.labels:
            if fences_remove and ex.labels[event] in FENCES:
                continue
            code += "\tunsigned char event_i" + event[-1] + ";\n"
        code += "\n"
        for event in ex.labels:
            if fences_remove and ex.labels[event] in FENCES:
                continue
            code += "\tevent_i" + event[-1] + " = nondet_uchar();\n"
        code += "\n"

        for event1 in ex.labels:
            for event2 in ex.labels:
                if fences_remove and (ex.labels[event1] in FENCES or ex.labels[event2] in FENCES):
                    continue
                if (ex.sequence[event1] < ex.sequence[event2]) and (ex.threads[event1] == ex.threads[event2]):
                    code += "\t__CPROVER_assume(event_i" + event1[-1] + " < event_i" + event2[-1] + ");\n"

        for event in ex.labels:
            if fences_remove and ex.labels[event] in FENCES:
                continue
            code += "\t__CPROVER_assume(event_i" + event[-1] + " < MAX_TIME);\n"

        code += "\n"
        code += "\t__CPROVER_assume(\n"

        for event in ex.labels:
            if ex.labels[event] == "WrReq":
                code += "\t\t\t\t(g_history[event_i" + event[-1] + "].type == " + ex.labels[event] + ") &&\n"
                code += "\t\t\t\t(g_history[event_i" + event[-1] + "].address == " + str(ex.location[event]) + ") &&\n"
                code += "\t\t\t\t(g_history[event_i" + event[-1] + "].data == " + str(ex.write_value[event]) + ") &&\n"
                code += "\t\t\t\t(g_history[event_i" + event[-1] + "].mdata == " + str(ex.mdata[event]) + ") &&\n"
                code += "\t\t\t\t(g_history[event_i" + event[-1] + "].channel == " + str(ex.channel[event]) + ") &&\n"
                code += "\n"
            if ex.labels[event] == "WrRsp":
                code += "\t\t\t\t(g_history[event_i" + event[-1] + "].type == " + ex.labels[event] + ") &&\n"
                code += "\t\t\t\t(g_history[event_i" + event[-1] + "].mdata == " + str(ex.mdata[event]) + ") &&\n"
                code += "\n"
            if ex.labels[event] == "RdReq":
                code += "\t\t\t\t(g_history[event_i" + event[-1] + "].type == " + ex.labels[event] + ") &&\n"
                code += "\t\t\t\t(g_history[event_i" + event[-1] + "].address == " + str(ex.location[event]) + ") &&\n"
                code += "\t\t\t\t(g_history[event_i" + event[-1] + "].mdata == " + str(ex.mdata[event]) + ") &&\n"
                code += "\t\t\t\t(g_history[event_i" + event[-1] + "].channel == " + str(ex.channel[event]) + ") &&\n"
                code += "\n"
            if ex.labels[event] == "RdRsp":
                code += "\t\t\t\t(g_history[event_i" + event[-1] + "].type == " + ex.labels[event] + ") &&\n"
                code += "\t\t\t\t(g_history[event_i" + event[-1] + "].address == " + str(ex.location[event]) + ") &&\n"
                code += "\t\t\t\t(g_history[event_i" + event[-1] + "].mdata == " + str(ex.mdata[event]) + ") &&\n"
                code += "\t\t\t\t(g_history[event_i" + event[-1] + "].channel == " + str(ex.channel[event]) + ") &&\n"
                code += "\n"
            if ex.labels[event] == "FnReq":
                if fences_remove:
                    nr_fences_removed = nr_fences_removed + 1
                    continue
                code += "\t\t\t\t(g_history[event_i" + event[-1] + "].type == " + ex.labels[event] + ") &&\n"
                code += "\t\t\t\t(g_history[event_i" + event[-1] + "].channel == " + str(ex.channel[event]) + ") &&\n"
                code += "\t\t\t\t(g_history[event_i" + event[-1] + "].mdata == " + str(ex.mdata[event]) + ") &&\n"
                code += "\n"
            if ex.labels[event] == "FnRsp":
                if fences_remove:
                    nr_fences_removed = nr_fences_removed + 1
                    continue
                code += "\t\t\t\t(g_history[event_i" + event[-1] + "].type == " + ex.labels[event] + ") &&\n"
                code += "\t\t\t\t(g_history[event_i" + event[-1] + "].channel == " + str(ex.channel[event]) + ") &&\n"
                code += "\t\t\t\t(g_history[event_i" + event[-1] + "].mdata == " + str(ex.mdata[event]) + ") &&\n"
                code += "\n"
            if ex.labels[event] == "FnReqAny":
                if fences_remove:
                    nr_fences_removed = nr_fences_removed + 1
                    continue
                code += "\t\t\t\t(g_history[event_i" + event[-1] + "].type == " + "FnReq" + ") &&\n"
                code += "\t\t\t\t(g_history[event_i" + event[-1] + "].channel == " + "VA" + ") &&\n"
                code += "\t\t\t\t(g_history[event_i" + event[-1] + "].mdata == " + str(ex.mdata[event]) + ") &&\n"
                code += "\n"
            if ex.labels[event] == "FnRspAny":
                if fences_remove:
                    nr_fences_removed = nr_fences_removed + 1
                    continue
                code += "\t\t\t\t(g_history[event_i" + event[-1] + "].type == " + "FnRsp" + ") &&\n"
                code += "\t\t\t\t(g_history[event_i" + event[-1] + "].channel == " + "VA" + ") &&\n"
                code += "\t\t\t\t(g_history[event_i" + event[-1] + "].mdata == " + str(ex.mdata[event]) + ") &&\n"
                code += "\n"
            if ex.labels[event] == "CpuRead":
                th_number = ex.threads[event]
                if ex.threads[event] == 2: th_number = 0
                code += "\t\t\t\t(g_history[event_i" + event[-1] + "].type == " + ex.labels[event] + ") &&\n"
                code += "\t\t\t\t(g_history[event_i" + event[-1] + "].address == " + str(ex.location[event]) + ") &&\n"
                code += "\t\t\t\t(g_history[event_i" + event[-1] + "].thread == " + str(th_number) + ") &&\n"
                code += "\n"
            if ex.labels[event] == "CpuWrite":
                th_number = ex.threads[event]
                if ex.threads[event] == 2: th_number = 0
                code += "\t\t\t\t(g_history[event_i" + event[-1] + "].type == " + ex.labels[event] + ") &&\n"
                code += "\t\t\t\t(g_history[event_i" + event[-1] + "].address == " + str(ex.location[event]) + ") &&\n"
                code += "\t\t\t\t(g_history[event_i" + event[-1] + "].data == " + str(ex.write_value[event]) + ") &&\n"
                code += "\t\t\t\t(g_history[event_i" + event[-1] + "].thread == " + str(th_number) + ") &&\n"
                code += "\n"
            if ex.labels[event] == "CpuFence":
                if fences_remove:
                    nr_fences_removed = nr_fences_removed + 1
                    continue
                th_number = ex.threads[event]
                if ex.threads[event] == 2: th_number = 0
                code += "\t\t\t\t(g_history[event_i" + event[-1] + "].type == " + ex.labels[event] + ") &&\n"
                code += "\t\t\t\t(g_history[event_i" + event[-1] + "].thread == " + str(th_number) + ") &&\n"
                code += "\n"

        cpu_writes = 0
        cpu_reads = 0
        fpga_writes = 0
        fpga_reads = 0
        for event in ex.labels:
            if ex.labels[event] in ["WrReq", "FnReq", "FnReqAny"]:
                if fences_remove and ex.labels[event] in FENCES:
                    continue
                fpga_writes += 1
            if ex.labels[event] in ["RdReq"]:
                fpga_reads += 1
            if ex.labels[event] in ["CpuWrite", "CpuFence"]:
                if fences_remove and ex.labels[event] in FENCES:
                    continue
                cpu_writes += 1
            if ex.labels[event] in ["CpuRead"]:
                cpu_reads += 1

        code += "\t\t\t\t(wrReq_issued == " + str(fpga_writes) + ") &&\n"
        code += "\t\t\t\t(rdReq_issued == " + str(fpga_reads) + ") &&\n"
        code += "\t\t\t\t(cpuWrites_issued == " + str(cpu_writes) + ") &&\n"
        code += "\t\t\t\t(cpuReads_issued == " + str(cpu_reads) + ") \n\t);\n"

        # code += "\t__CPROVER_assert(0, \"False\");\n"

        code += "\t__CPROVER_assume(wrBuffer1.num_pending_operations == 0);\n"
        code += "\t__CPROVER_assume(wrBuffer2.num_pending_operations == 0);\n"
        code += "\t__CPROVER_assume(wrReqPool.num_pending_operations == 0);\n"
        code += "\t__CPROVER_assume(rdReqPool.num_pending_operations == 0);\n"
        code += "\t__CPROVER_assume(upstreamChannels[0].num_pending_operations == 0);\n"
        code += "\t__CPROVER_assume(upstreamChannels[1].num_pending_operations == 0);\n"
        code += "\t__CPROVER_assume(downstreamChannels[0].num_pending_operations == 0);\n"
        code += "\t__CPROVER_assume(downstreamChannels[1].num_pending_operations == 0);\n\n"

        read_list = []
        write_list = []
        for event in ex.labels:
            if ex.labels[event] in ["RdRsp", "CpuRead"]:
                read_vertex = ex.graph.get_first_node(event, "rf")
                read_list.append("g_history[event_i" + event[-1] + "].data")
                if read_vertex:
                    write_list.append("g_history[event_i" + read_vertex[-1] + "].data")
                else:
                    write_list.append("0")

        code += "\t__CPROVER_assert( !(\n"

        for event in ex.labels:
            if ex.labels[event] in ["WrRsp", "CpuWrite"] and not ex.graph.get_outer_degree(event, "co"):
                code += "\t\t\t\t(sharedMemory[" + str(ex.location[event]) + "] "
                code += " == g_history[event_i" + event[-1] + "].data) &&\n"

        for i in range(len(read_list) - 1):
            code += "\t\t\t\t(" + read_list[i] + " == " + write_list[i] + ") &&\n"
        code += "\t\t\t\t(" + read_list[-1] + " == " + write_list[-1] + ") ),\n"
        code += "\t\t\t\t\"Alloy trace " + str(number) + "\");\n"

        code += "}\n\n"
        return code, cpu_writes, cpu_reads, fpga_writes, fpga_reads, nr_fences_removed

    def generate_traces(self, fences_remove=False):

        code = "#include \"alloy_traces.h\"\n"
        code += "unsigned char nondet_uchar();\n\n"

        code += "extern unsigned char sharedMemory[MAX_LOC];\n\n"
        code += "extern WrBuffer wrBuffer1;\n"
        code += "extern WrBuffer wrBuffer2;\n\n"
        code += "extern ReqPool wrReqPool;\n"
        code += "extern ReqPool rdReqPool;\n\n"
        code += "extern Channel upstreamChannels[MAX_CHANNELS];\n"
        code += "extern Channel downstreamChannels[MAX_CHANNELS];\n\n"

        valid_traces = []
        cpu_writes = []
        cpu_reads = []
        fpga_writes = []
        fpga_reads = []
        for i, ex in enumerate(self._executions):
            if ex.get_number_cpu_threads > self.CBMC_CPU_THREADS or \
                    ex.get_number_fpga_threads > self.CBMC_FPGA_THREADS or \
                    ex.get_number_locations > self.CBMC_VARIABLES:
                continue
            new_code, cw, cr, fw, fr, nr_removed_fenes = self.cbmc_trace(i, ex, fences_remove=fences_remove)
            if fences_remove and nr_removed_fenes == 0:
                continue
            code += self.pretty_print(ex)
            code += new_code
            cpu_writes.append(cw)
            cpu_reads.append(cr)
            fpga_writes.append(fw)
            fpga_reads.append(fr)
            valid_traces.append(i)

        self.alloy_traces_c = code

        code = "#ifndef ALLOY_TRACES_H_\n"
        code += "#define ALLOY_TRACES_H_\n\n"
        code += "#include \"actors.h\"\n\n"
        code += "void alloy_traces() {\n\n"
        code += "\tif (nondet_int()) {\n"

        for i in range(len(valid_traces)):
            code += "\t} else if (nondet_int()) {\n"
            code += "#ifdef TRACE_" + str(valid_traces[i]) + "\n"
            code += "#define MAX_CPU_WRITES " + str(cpu_writes[i]) + "\n"
            code += "#define MAX_CPU_READS " + str(cpu_reads[i]) + "\n"
            code += "#define MAX_WR_REQ " + str(fpga_writes[i]) + "\n"
            code += "#define MAX_RD_REQ " + str(fpga_reads[i]) + "\n"
            code += "\t\ttrace_" + str(valid_traces[i]) + "();\n"
            code += "#endif\n"
        code += "\t}\n"
        code += "}\n"

        code += "#endif"

        self.alloy_traces_h = code

        return valid_traces


class Generate:
    """
    Generate the litmus test structure
    """
    CBMC_H_FILE = "../model/CBMC/harp/alloy_traces.h"
    CBMC_C_FILE = "../model/CBMC/harp/alloy_traces.c"

    def __init__(self, max_traces=None, unique=True, shuffle=False):
        """
        :param max_traces: Maximum traces to generate
        :param unique: True if we activate the duplicate removal
        :param shuffle: Shuffle the executions
        :return: None
        """
        traces = TracesList()
        traces.populate_list(maximum_traces=max_traces, unique=unique, shuffle=shuffle)

        self.cbmc_c_file = self.CBMC_C_FILE
        self.cbmc_h_file = self.CBMC_H_FILE

        if unique:
            self.cbmcTests = CbmcTests(executions=traces.unique_executions)
            self.hardwareTests = HardwareTests(executions=traces.unique_executions)
        else:
            self.cbmcTests = CbmcTests(executions=traces.executions)
            self.hardwareTests = HardwareTests(executions=traces.executions)

    def generate_cbmc_traces(self, cbmc_h_file=None, cbmc_c_file=None, fences_remove=False):
        """
        Generates the first "traces" for CBMC
        :param cbmc_h_file: Overwrite default cbmc_h_file
        :param cbmc_c_file: Overwrite default cbmc_c_file
        :param fences_remove: Generate only the traces with fences removed
        :return: None
        """
        if cbmc_c_file:
            self.cbmc_c_file = cbmc_c_file
        if cbmc_h_file:
            self.cbmc_h_file = cbmc_h_file

        generated_traces = self.cbmcTests.generate_traces(fences_remove=fences_remove)

        with open(self.cbmc_h_file, "w") as cbmc_h:
            cbmc_h.write(self.cbmcTests.alloy_traces_h)

        with open(self.cbmc_c_file, "w") as cbmc_c:
            cbmc_c.write(self.cbmcTests.alloy_traces_c)

        print(str(len(generated_traces)) + " CBMC traces written to ")
        print("\t" + self.cbmc_h_file)
        print("\t" + self.cbmc_c_file)
        return generated_traces

    def generate_hardware_traces(self, fences_remove=False):
        """
        Generate the hardware traces
        """
        print("Generating hardware traces")
        return self.hardwareTests.create_all_traces(fences_remove)


class RunCbmcTests:
    CBMC_FOLDER = "../model/CBMC/harp/"
    UNWIND_ASSERTIONS = " --unwinding-assertions"
    BUILD_FOLDER = "BUILD"
    COMPILE_LIMIT = 100

    def __init__(self, traces, rep, unwinding, cores, define1="-DALLOY_TRACES", define2="-DTRACE_", filename="alloy_trace.c"):
        self._traces = traces
        self.rep = rep
        self.unwind = int(unwinding)
        self.cores = int(cores)

        self.define1 = define1
        self.define2 = define2
        self.filename = filename

        if not os.path.exists(self.BUILD_FOLDER):
            os.makedirs(self.BUILD_FOLDER)

    def run_cbmc(self, trace):
        cmd = "cbmc "
        cmd += self.CBMC_FOLDER + self.BUILD_FOLDER + "/trace_" + str(trace)
        cmd += " --unwind " + str(self.unwind) + self.UNWIND_ASSERTIONS
        print(cmd)
        stream = os.popen(cmd)
        output = stream.read()
        if output.find("VERIFICATION SUCCESSFUL") != -1:
            print(colored("Trace " + str(trace) + " was NOT reproducible", NOT_REPRODUCIBLE_COLOR))
            return trace
        else:
            print(colored("Trace " + str(trace) + " was reproducible", REPRODUCIBLE_COLOR))
            return -1

    def compile_test(self, trace):
        cmd = ""
        cmd += "goto-cc " + self.define1 + " " + self.define2 + str(trace)
        cmd += " " + self.CBMC_FOLDER + self.BUILD_FOLDER + "/actors.o "
        cmd += " " + self.CBMC_FOLDER + "harp.c "
        cmd += " " + self.CBMC_FOLDER + self.filename
        cmd += " -o " + self.CBMC_FOLDER + self.BUILD_FOLDER + "/trace_" + str(trace)
        print(cmd)
        os.system(cmd)

    def run_tests(self):
        cmd = "goto-cc -c " + self.CBMC_FOLDER + "actors.c -o " + self.CBMC_FOLDER + self.BUILD_FOLDER + "/actors.o"
        print(cmd)
        os.system(cmd)

        with Pool(self.cores) as p:
            p.map(self.compile_test, self._traces)

        with Pool(self.cores) as p:
            unreproducible_traces = list(tqdm(p.imap(self.run_cbmc, self._traces), total=len(self._traces)))

        if sorted(self._traces) == sorted(unreproducible_traces):
            print("\nAll traces could NOT be reproduced")
            return
        if sum(1 for i in unreproducible_traces if i == -1) == len(self._traces):
            print("\nAll traces could be reproduced")
            return

        if not self.rep:
            for i in self._traces:
                if i not in unreproducible_traces:
                    print(colored("Trace " + str(i) + " could NOT be reproduced", NOT_REPRODUCIBLE_COLOR))
        else:
            for i in self._traces:
                if i in unreproducible_traces:
                    print(colored("Trace " + str(i) + "could be reproduced", REPRODUCIBLE_COLOR))


class RunHardwareTests:

    def __init__(self, traces, repetitions=10, vl0_enemy=None, vh0_enemy=None, vh1_enemy=None):
        self._traces = traces
        self._repetitions = repetitions
        self._vl0_enemy = vl0_enemy
        self._vh0_enemy = vh0_enemy
        self._vh1_enemy = vh1_enemy

    def run_tests(self):
        failed_traces=[]

        for trace in self._traces:
            cmd = "fpgaconf litmus_tests/test/hw/build_fpga/litmus_processor.gbs"
            print(cmd)
            os.system(cmd)

            (folder, executable) = trace
            os.chdir(folder)
            print("Running make in folder " + folder)
            os.system("make")
            command = "./" + executable
            if self._repetitions:
                command += " -r " + str(self._repetitions)
            if self._vl0_enemy:
                command += " --VL0_enemy " + self._vl0_enemy
            if self._vh0_enemy:
                command += " --VH0_enemy " + self._vh0_enemy
            if self._vh1_enemy:
                command += " --VH1_enemy " + self._vh1_enemy
            print(command)
            exit_code = os.system(command)
            print("Exit code " + str(exit_code))
            if exit_code:
                failed_traces.append(executable)
            os.chdir("../../..")
        if failed_traces:
            print("The fallowing traces failed:")
            for trace in failed_traces:
                print(trace)
        else:
            print("Great success!!!!")

def print_help():
    print('backend.py')
    print("\t -h, --help\t\t\t Print this message")
    print("\t -d, --duplicates\t\t Keep the duplicates")
    print("\t -r, --reproducible\t\t Expect the traces to be reproducible")
    print("\t -u, --unwind\t\t\t How many times to unwind")
    print("\t -m, --max_traces\t\t Limit the amount of traces")
    print("\t -f, --fences_remove\t\t Remove fences")
    print("\t -c, --cores\t\t Number of cores")
    print("\t --cbmc\t\t Generate cbmc traces")
    print("\t --run_cbmc\t\t Run cbmc traces")
    print("\t --hardware\t\t Generate hardware traces")
    print("\t --run_hardware\t\t Run hardware traces")
    print("\t --repeat\t\t Repeat hardware experiments \"repeat\" times")
    print("\t --vl0_enemy\t\t Run hardware traces with vl0_enemy")
    print("\t --vh0_enemy\t\t Run hardware traces with vh0_enemy")
    print("\t --vh1_enemy\t\t Run hardware traces with vh1_enemy")
    print("\t -s, --shuffle\t\t S")


if __name__ == '__main__':

    duplicate_removal = True
    expect_reproducible = False
    maximum_traces = None
    fences_remove = False
    unwind = 25
    cores = 4
    cbmcTraces = False
    run_cbmcTraces = False
    hardwareTraces = False
    run_hardwareTraces = False
    repeat = 10
    vl0_enemy = None
    vh0_enemy = None
    vh1_enemy = None
    shuffle = False
    manual_traces = False
    queue_traces = False

    try:
        opts, args = getopt.getopt(sys.argv[1:], "hdru:m:fc:s", ["help",
                                                                 "duplicates",
                                                                 "reproducible",
                                                                 "unwind=",
                                                                 "max_traces=",
                                                                 "fences_remove",
                                                                 "cores=",
                                                                 "cbmc",
                                                                 "run_cbmc",
                                                                 "hardware",
                                                                 "run_hardware",
                                                                 "repeat=",
                                                                 "vl0_enemy=",
                                                                 "vh0_enemy=",
                                                                 "vh1_enemy=",
                                                                 "shuffle",
                                                                 "manual_traces",
                                                                 "queue_traces"])
    except getopt.GetoptError:
        print_help()
        sys.exit(2)

    for opt, arg in opts:
        if opt in ("-h", "--help"):
            print_help()
            sys.exit()
        elif opt in ("-d", "--duplicates"):
            duplicate_removal = False
        elif opt in ("-r", "--reproducible"):
            expect_reproducible = True
        elif opt in ("-u", "--unwind"):
            unwind = arg
        elif opt in ("-m", "--max_traces"):
            maximum_traces = arg
        elif opt in ("-f", "--fences_remove"):
            fences_remove = True
        elif opt in ("-c", "--cores"):
            cores = arg
        elif opt in "--cbmc":
            cbmcTraces = True
        elif opt in "--run_cbmc":
            run_cbmcTraces = True
        elif opt in "--hardware":
            hardwareTraces = True
        elif opt in "--run_hardware":
            run_hardwareTraces = True
        elif opt in "--repeat":
            repeat = arg
        elif opt in "--vl0_enemy":
            vl0_enemy = arg
        elif opt in "--vh0_enemy":
            vh0_enemy = arg
        elif opt in "--vh1_enemy":
            vh1_enemy = arg
        elif opt in ("-s", "--shuffle"):
            shuffle = True
        elif opt in "--manual_traces":
            manual_traces = True
        elif opt in "--queue_traces":
            queue_traces = True

    # This mode verifies the traces from the manual
    if manual_traces:
        print(colored("Running FPGA-only allowed traces from manual", MESSAGE_COLOR))
        run_cbmc = RunCbmcTests(traces=[1, 5, 6, 8, 11],
                                rep=True,
                                unwinding=unwind,
                                cores=cores,
                                define1="-DTESTS_FPGA",
                                define2="-DFPGA_TEST_",
                                filename="tests_fpga.c")
        #run_cbmc.run_tests()

        print(colored("Running FPGA-only disallowed traces from manual", MESSAGE_COLOR))
        run_cbmc = RunCbmcTests(traces=[2, 3, 4, 7, 9, 10],
                                rep=False,
                                unwinding=unwind,
                                cores=cores,
                                define1="-DTESTS_FPGA",
                                define2="-DFPGA_TEST_",
                                filename="tests_fpga.c")
        #run_cbmc.run_tests()

        print(colored("Running CPU/FPGA-only allowed traces from manual", MESSAGE_COLOR))
        run_cbmc = RunCbmcTests(traces=[2, 3, 5],
                                rep=True,
                                unwinding=unwind,
                                cores=cores,
                                define1="-DTESTS_CPU_FPGA",
                                define2="-DFPGA_CPU_TEST_",
                                filename="tests_cpu_fpga.c")
        run_cbmc.run_tests()

        print(colored("Running CPU/FPGA-only disallowed traces from manual", MESSAGE_COLOR))
        run_cbmc = RunCbmcTests(traces=[1, 4, 6],
                                rep=True,
                                unwinding=unwind,
                                cores=cores,
                                define1="-DTESTS_CPU_FPGA",
                                define2="-DFPGA_CPU_TEST_",
                                filename="tests_cpu_fpga.c")
        run_cbmc.run_tests()

        exit()

    # This verifies that the queue implementation
    if queue_traces:
        print(colored("Verifying the basic operations of the queue", MESSAGE_COLOR))
        run_cbmc = RunCbmcTests(traces=[1, 2, 3, 4, 5, 6, 7, 8],
                                rep=False,
                                unwinding=unwind,
                                cores=cores,
                                define1="-DTESTS_QUEUE",
                                define2="-DQUEUE_TEST_",
                                filename="tests_queue.c")
        run_cbmc.run_tests()
        exit()

    # The generic mode
    gen = Generate(max_traces=maximum_traces, unique=duplicate_removal)

    if cbmcTraces:
        all_traces = gen.generate_cbmc_traces(fences_remove=fences_remove)

        if run_cbmcTraces:
            run_cbmc = RunCbmcTests(traces=all_traces, rep=expect_reproducible, unwinding=unwind, cores=cores)
            run_cbmc.run_tests()

    if hardwareTraces:
        hardware_traces = gen.generate_hardware_traces(fences_remove=fences_remove)
        if run_hardwareTraces:
            run_hardware = RunHardwareTests(hardware_traces, repeat, vl0_enemy, vh0_enemy, vh1_enemy)
            run_hardware.run_tests()
