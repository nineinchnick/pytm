import argparse
import json
import logging
import os
import random
import uuid
from collections import defaultdict
from hashlib import sha224
from re import match
from sys import exit, stderr
from textwrap import wrap
from weakref import WeakKeyDictionary

from .template_engine import SuperFormatter

''' Helper functions '''

''' The base for this (descriptors instead of properties) has been shamelessly lifted from https://nbviewer.jupyter.org/urls/gist.github.com/ChrisBeaumont/5758381/raw/descriptor_writeup.ipynb
    By Chris Beaumont
'''


logger = logging.getLogger(__name__)


class var(object):
    ''' A descriptor that allows setting a value only once '''
    def __init__(self, default, onSet=None):
        self.default = default
        self.data = WeakKeyDictionary()
        self.onSet = onSet

    def __get__(self, instance, owner):
        # when x.d is called we get here
        # instance = x
        # owner = type(x)
        return self.data.get(instance, self.default)

    def __set__(self, instance, value):
        # called when x.d = val
        # instance = x
        # value = val
        if instance in self.data:
            raise ValueError(
                "cannot overwrite {} value with {}, already set to {}".format(
                    self.__class__.__name__, value, self.data[instance]
                )
            )
        self.data[instance] = value
        if self.onSet is not None:
            self.onSet(instance, value)


class varString(var):
    def __set__(self, instance, value):
        if not isinstance(value, str):
            raise ValueError("expecting a String value, got a {}".format(type(value)))
        super().__set__(instance, value)


class varBoundary(var):
    def __set__(self, instance, value):
        if not isinstance(value, Boundary):
            raise ValueError("expecting a Boundary value, got a {}".format(type(value)))
        super().__set__(instance, value)


class varBool(var):
    def __set__(self, instance, value):
        if not isinstance(value, bool):
            raise ValueError("expecting a boolean value, got a {}".format(type(value)))
        super().__set__(instance, value)


class varInt(var):
    def __set__(self, instance, value):
        if not isinstance(value, int):
            raise ValueError("expecting an integer value, got a {}".format(type(value)))
        super().__set__(instance, value)


class varElement(var):
    def __set__(self, instance, value):
        if not isinstance(value, Element):
            raise ValueError("expecting an Element (or inherited) "
                             "value, got a {}".format(type(value)))
        super().__set__(instance, value)


class varElements(var):
    def __init__(self, default=None, onSet=None):
        super().__init__(default, onSet=onSet)
        if self.default is None:
            self.default = []

    def __set__(self, instance, value):
        for i, e in enumerate(value):
            if not isinstance(e, Element):
                raise ValueError(
                    "expecting a list of Elements, item number {} is a {}".format(
                        type(value)
                    )
                )
        super().__set__(instance, list(value))


def _setColor(element):
    if element.inScope is True:
        return "black"
    else:
        return "grey69"


def _setLabel(element):
    return "<br/>".join(wrap(element.name, 14))


def _sort(flows, addOrder=False):
    ordered = sorted(flows, key=lambda flow: flow.order)
    if not addOrder:
        return ordered
    for i, flow in enumerate(ordered):
        if flow.order != -1:
            break
        ordered[i].order = i + 1
    return ordered


def _match_responses(flows):
    """Ensure that responses are pointing to requests"""
    index = defaultdict(list)
    for e in flows:
        key = (e.source, e.sink)
        index[key].append(e)
    for e in flows:
        if e.responseTo is not None:
            if not e.isResponse:
                e.isResponse = True
            if e.responseTo.response is None:
                e.responseTo.response = e
        if e.response is not None:
            if not e.response.isResponse:
                e.response.isResponse = True
            if e.response.responseTo is None:
                e.response.responseTo = e

    for e in flows:
        if not e.isResponse or e.responseTo is not None:
            continue
        key = (e.sink, e.source)
        if len(index[key]) == 1:
            e.responseTo = index[key][0]
            index[key][0].response = e

    return flows


def _apply_defaults(elements):
    for e in elements:
        e._safeset("data", e.source.data)
        if e.isResponse:
            e._safeset("protocol", e.source.protocol)
            e._safeset("srcPort", e.source.port)
            e._safeset("isEncrypted", e.source.isEncrypted)
        else:
            e._safeset("protocol", e.sink.protocol)
            e._safeset("dstPort", e.sink.port)
            if hasattr(e.sink, "isEncrypted"):
                e._safeset("isEncrypted", e.sink.isEncrypted)


def _sort_elements(elements):
    ''' sort elements by order in which they appear in dataflows '''
    if not elements:
        return elements
    orders = {}
    for e in elements:
        if not hasattr(e, "order"):
            continue
        if e.source not in orders or orders[e.source] > e.order:
            orders[e.source] = e.order
    m = max(orders.values()) + 1
    # sort in this order:
    # assets in order in which they appear in dataflows
    # dataflows in order
    # other types not assigned to dataflows (boundaries), by name
    return sorted(
        elements,
        key=lambda e: (
            orders.get(e, m),
            e.__class__.__name__,
            getattr(e, "order", 0),
            str(e),
        ),
    )


''' End of help functions '''


class Threat():
    id = varString("")
    description = varString("")
    condition = varString("")
    details = varString("")
    severity = varString("")
    mitigations = varString("")
    example = varString("")
    references = varString("")
    target = ()

    ''' Represents a possible threat '''
    def __init__(self, json_read):
        self.id = json_read['SID']
        self.description = json_read['description']
        self.condition = json_read['condition']
        self.target = json_read['target']
        self.details = json_read['details']
        self.severity = json_read['severity']
        self.mitigations = json_read['mitigations']
        self.example = json_read['example']
        self.references = json_read['references']

    def apply(self, target):
        if type(self.target) is list:
            if target.__class__.__name__ not in self.target:
                return None
        else:
            if target.__class__.__name__ is not self.target:
                return None
        return eval(self.condition)


class Finding():
    ''' This class represents a Finding - the element in question and a description of the finding '''
    def __init__(
        self,
        element,
        description=None,
        details=None,
        severity=None,
        mitigations=None,
        example=None,
        id=None,
        references=None,
        threat=None,
    ):
        self.target = element
        self.description = description
        self.details = details
        self.severity = severity
        self.mitigations = mitigations
        self.example = example
        self.id = id
        self.references = threat.references
        if threat is not None:
            self.description = threat.description
            self.details = threat.details
            self.severity = threat.severity
            self.mitigations = threat.mitigations
            self.example = threat.example
            self.id = threat.id
            self.references = threat.references


class TM():
    ''' Describes the threat model administratively, and holds all details during a run '''
    _sf = None
    elements = varElements(onSet=lambda i, v: i._init_elements())
    description = varString("")
    threatsFile = varString(
        os.path.join(os.path.dirname(__file__), "threatlib", "threats.json"),
        onSet=lambda i, v: i._init_threats(),
    )
    isOrdered = varBool(False, onSet=lambda i, v: i._init_elements())
    mergeResponses = varBool(False)

    def __init__(self, name, **kwargs):
        self._threats = []
        self._findings = []
        self._threatsExcluded = []
        self._sf = SuperFormatter()
        for key, value in kwargs.items():
            setattr(self, key, value)
        self.name = name
        self._add_threats()

    def _init_elements(self):
        self._flows = []
        self._boundaries = []
        self._elements = []
        # first find all Dataflows to retain order
        for e in self.elements:
            if isinstance(e, Dataflow):
                self._flows.append(e)
            if isinstance(e, Boundary) and e not in self._boundaries:
                self._boundaries.append(e)
        # elements can contain Boundaries and Dataflows so create a complete set
        # including their elements, source and sink
        all_elements = set(self.elements)
        for e in self.elements:
            try:
                all_elements |= set(e.elements)
            except AttributeError:
                pass
            try:
                all_elements.add(e.source)
                if e.source.inBoundary is not None:
                    all_elements.add(e.source.inBoundary)
                all_elements.add(e.sink)
                if e.sink.inBoundary is not None:
                    all_elements.add(e.sink.inBoundary)
            except AttributeError:
                pass

        _apply_defaults(self._flows)
        self._flows = _match_responses(_sort(self._flows, self.isOrdered))
        self._elements = _sort_elements(all_elements)

        # gather elements that need to be assigned to boundaries
        boundElements = defaultdict(list)
        for e in self._elements:
            try:
                if e.inBoundary is None:
                    continue
            except AttributeError:
                continue
            if e.inBoundary not in self._boundaries:
                self._boundaries.append(e.inBoundary)
            if e not in e.inBoundary.elements:
                boundElements[e.inBoundary].append(e)

        for boundary, elements in boundElements.items():
            # if boundary was initiated with any elements, this will throw an exception
            boundary.elements = elements

    def _init_threats(self):
        self._threats = []
        self._add_threats()

    def _add_threats(self):
        with open(self.threatsFile, "r", encoding="utf8") as threat_file:
            threats_json = json.load(threat_file)

        for i in threats_json:
            self._threats.append(Threat(i))

    def resolve(self):
        for e in self._elements:
            if not e.inScope:
                continue
            for t in self._threats:
                if not t.apply(e):
                    continue
                self._findings.append(Finding(e.name, threat=t))

    def check(self):
        if self.description is None:
            raise ValueError(
                "Every threat model should have at least "
                "a brief description of the system being modeled."
            )
        result = True
        for e in self._elements:
            if not e.check():
                result = False
        return result

    def dfd(self):
        print("digraph tm {\n\tgraph [\n\tfontname = Arial;\n\tfontsize = 14;\n\t]")
        print("\tnode [\n\tfontname = Arial;\n\tfontsize = 14;\n\trankdir = lr;\n\t]")
        print("\tedge [\n\tshape = none;\n\tfontname = Arial;\n\tfontsize = 12;\n\t]")
        print('\tlabelloc = "t";\n\tfontsize = 20;\n\tnodesep = 1;\n')
        for b in self._boundaries:
            b.dfd()
        if self.mergeResponses:
            for e in self._flows:
                if e.response is not None:
                    e.response._is_drawn = True
        for e in self._elements:
            if not e._is_drawn and e.inBoundary is None:
                e.dfd(mergeResponses=self.mergeResponses)
        print("}")

    def seq(self):
        print("@startuml")
        for e in self._elements:
            if isinstance(e, Actor):
                print("actor {0} as \"{1}\"".format(e._uniq_name(), e.name))
            elif isinstance(e, Datastore):
                print("database {0} as \"{1}\"".format(e._uniq_name(), e.name))
            elif not isinstance(e, Dataflow) and not isinstance(e, Boundary):
                print("entity {0} as \"{1}\"".format(e._uniq_name(), e.name))

        for e in self._flows:
            print("{0} -> {1}: {2}".format(e.source._uniq_name(), e.sink._uniq_name(), e.name))
            if e.note != "":
                print("note left\n{}\nend note".format(e.note))
        print("@enduml")

    def report(self, *args, **kwargs):
        result = get_args()
        self._template = result.report
        with open(self._template) as file:
            template = file.read()

        output = self._sf.format(
            template,
            tm=self,
            dataflows=self._flows,
            threats=self._threats,
            findings=self._findings,
            elements=self._elements,
            boundaries=self._boundaries,
        )
        print(output)

    def process(self):
        self.check()
        result = get_args()
        logging.basicConfig(level=logging.INFO, format="%(levelname)s: %(message)s")
        if result.debug:
            logger.setLevel(logging.DEBUG)
        if result.seq is True:
            self.seq()
        if result.dfd is True:
            self.dfd()
        if result.report is not None:
            self.resolve()
            self.report()
        if result.exclude is not None:
            self._threatsExcluded = result.exclude.split(",")
        if result.describe is not None:
            try:
                one_word = result.describe.split()[0]
                c = eval(one_word)
            except Exception:
                stderr.write("No such class to describe: {}\n".format(result.describe))
                exit(-1)
            print("The following properties are available for " + result.describe)
            [print("\t{}".format(i)) for i in dir(c) if not callable(i) and match("__", i) is None]
        if result.list is True:
            [print("{} - {}".format(t.id, t.description)) for t in self._threats]
            exit(0)


class Element():
    name = varString("")
    description = varString("")
    inBoundary = varBoundary(None)
    onAWS = varBool(False)
    isHardened = varBool(False)
    inScope = varBool(True)
    implementsAuthenticationScheme = varBool(False)
    implementsNonce = varBool(False)
    handlesResources = varBool(False)
    definesConnectionTimeout = varBool(False)
    OS = varString("")
    isAdmin = varBool(False)

    def __init__(self, name, **kwargs):
        for key, value in kwargs.items():
            setattr(self, key, value)
        self.name = name
        self.uuid = uuid.UUID(int=random.getrandbits(128))
        self._is_drawn = False

    def __repr__(self):
        return "<{0}.{1}({2}) at {3}>".format(
            self.__module__, type(self).__name__, self.name, hex(id(self))
        )

    def __str__(self):
        return '{0}({1})'.format(type(self).__name__, self.name)

    def _uniq_name(self):
        ''' transform name and uuid into a unique string '''
        h = sha224(str(self.uuid).encode('utf-8')).hexdigest()
        name = "".join(x for x in self.name if x.isalpha())
        return "{0}_{1}_{2}".format(type(self).__name__.lower(), name, h[:10])

    def check(self):
        ''' makes sure it is good to go '''
        return True

    def dfd(self, **kwargs):
        self._is_drawn = True
        label = _setLabel(self)
        print("%s [\n\tshape = square;" % self._uniq_name())
        print('\tlabel = <<table border="0" cellborder="0" cellpadding="2"><tr><td><b>{0}</b></td></tr></table>>;'.format(label))
        print("]")

    def _safeset(self, attr, value):
        try:
            setattr(self, attr, value)
        except ValueError:
            pass


class Lambda(Element):
    onAWS = varBool(True)
    authenticatesSource = varBool(False)
    hasAccessControl = varBool(False)
    sanitizesInput = varBool(False)
    encodesOutput = varBool(False)
    handlesResourceConsumption = varBool(False)
    authenticationScheme = varString("")
    usesEnvironmentVariables = varBool(False)
    validatesInput = varBool(False)
    checksInputBounds = varBool(False)
    environment = varString("")
    implementsAPI = varBool(False)
    authorizesSource = varBool(False)
    data = varString("")

    def __init__(self, name, **kwargs):
        super().__init__(name, **kwargs)

    def dfd(self, **kwargs):
        self._is_drawn = True
        color = _setColor(self)
        pngpath = os.path.dirname(__file__) + "/images/lambda.png"
        label = _setLabel(self)
        print('{0} [\n\tshape = none\n\tfixedsize=shape\n\timage="{2}"\n\timagescale=true\n\tcolor = {1}'.format(self._uniq_name(), color, pngpath))
        print('\tlabel = <<table border="0" cellborder="0" cellpadding="2"><tr><td><b>{}</b></td></tr></table>>;'.format(label))
        print("]")


class Server(Element):
    port = varInt(-1)
    isEncrypted = varBool(False)
    protocol = varString("")
    data = varString("")
    providesConfidentiality = varBool(False)
    providesIntegrity = varBool(False)
    authenticatesSource = varBool(False)
    authenticatesDestination = varBool(False)
    sanitizesInput = varBool(False)
    encodesOutput = varBool(False)
    hasAccessControl = varBool(False)
    implementsCSRFToken = varBool(False)
    handlesResourceConsumption = varBool(False)
    authenticationScheme = varString("")
    validatesInput = varBool(False)
    validatesHeaders = varBool(False)
    encodesHeaders = varBool(False)
    usesSessionTokens = varBool(False)
    usesEncryptionAlgorithm = varString("")
    usesCache = varBool(False)
    usesVPN = varBool(False)
    authorizesSource = varBool(False)
    usesCodeSigning = varBool(False)
    validatesContentType = varBool(False)
    invokesScriptFilters = varBool(False)
    usesStrongSessionIdentifiers = varBool(False)
    usesLatestTLSversion = varBool(False)
    implementsServerSideValidation = varBool(False)
    usesXMLParser = varBool(False)
    disablesDTD = varBool(False)
    checksInputBounds = varBool(False)
    implementsStrictHTTPValidation = varBool(False)

    def __init__(self, name, **kwargs):
        super().__init__(name, **kwargs)

    def dfd(self, **kwargs):
        self._is_drawn = True
        color = _setColor(self)
        label = _setLabel(self)
        print("{0} [\n\tshape = circle\n\tcolor = {1}".format(self._uniq_name(), color))
        print('\tlabel = <<table border="0" cellborder="0" cellpadding="2"><tr><td><b>{}</b></td></tr></table>>;'.format(label))
        print("]")


class ExternalEntity(Element):
    hasPhysicalAccess = varBool(False)

    def __init__(self, name, **kwargs):
        super().__init__(name, **kwargs)


class Datastore(Element):
    port = varInt(-1)
    isEncrypted = varBool(False)
    protocol = varString("")
    data = varString("")
    onRDS = varBool(False)
    storesLogData = varBool(False)
    storesPII = varBool(False)
    storesSensitiveData = varBool(False)
    isSQL = varBool(True)
    providesConfidentiality = varBool(False)
    providesIntegrity = varBool(False)
    authenticatesSource = varBool(False)
    authenticatesDestination = varBool(False)
    isShared = varBool(False)
    hasWriteAccess = varBool(False)
    handlesResourceConsumption = varBool(False)
    isResilient = varBool(False)
    handlesInterruptions = varBool(False)
    authorizesSource = varBool(False)
    hasAccessControl = varBool(False)
    authenticationScheme = varString("")
    usesEncryptionAlgorithm = varString("")
    validatesInput = varBool(False)
    implementsPOLP = varBool(False)

    def __init__(self, name, **kwargs):
        super().__init__(name, **kwargs)

    def dfd(self, **kwargs):
        self._is_drawn = True
        color = _setColor(self)
        label = _setLabel(self)
        print("{0} [\n\tshape = none;\n\tcolor = {1};".format(self._uniq_name(), color))
        print('\tlabel = <<table sides="TB" cellborder="0" cellpadding="2"><tr><td><font color="{1}"><b>{0}</b></font></td></tr></table>>;'.format(label, color))
        print("]")


class Actor(Element):
    port = varInt(-1)
    protocol = varString("")
    data = varString("")

    def __init__(self, name, **kwargs):
        super().__init__(name, **kwargs)

    def dfd(self, **kwargs):
        self._is_drawn = True
        label = _setLabel(self)
        print("%s [\n\tshape = square;" % self._uniq_name())
        print('\tlabel = <<table border="0" cellborder="0" cellpadding="2"><tr><td><b>{0}</b></td></tr></table>>;'.format(label))
        print("]")


class Process(Element):
    port = varInt(-1)
    isEncrypted = varBool(False)
    protocol = varString("")
    data = varString("")
    codeType = varString("Unmanaged")
    implementsCommunicationProtocol = varBool(False)
    providesConfidentiality = varBool(False)
    providesIntegrity = varBool(False)
    authenticatesSource = varBool(False)
    authenticatesDestination = varBool(False)
    isResilient = varBool(False)
    hasAccessControl = varBool(False)
    tracksExecutionFlow = varBool(False)
    implementsCSRFToken = varBool(False)
    handlesResourceConsumption = varBool(False)
    handlesCrashes = varBool(False)
    handlesInterruptions = varBool(False)
    authorizesSource = varBool(False)
    authenticationScheme = varString("")
    checksInputBounds = varBool(False)
    validatesInput = varBool(False)
    sanitizesInput = varBool(False)
    implementsAPI = varBool(False)
    usesSecureFunctions = varBool(False)
    environment = varString("")
    usesEnvironmentVariables = varBool(False)
    disablesiFrames = varBool(False)
    implementsPOLP = varBool(False)
    encodesOutput = varBool(False)
    usesParameterizedInput = varBool(False)
    allowsClientSideScripting = varBool(False)
    usesStrongSessionIdentifiers = varBool(False)
    encryptsCookies = varBool(False)
    usesMFA = varBool(False)
    encryptsSessionData = varBool(False)
    verifySessionIdentifiers = varBool(False)

    def __init__(self, name, **kwargs):
        super().__init__(name, **kwargs)

    def dfd(self, **kwargs):
        self._is_drawn = True
        color = _setColor(self)
        label = _setLabel(self)
        print("{0} [\n\tshape = circle;\n\tcolor = {1};\n".format(self._uniq_name(), color))
        print('\tlabel = <<table border="0" cellborder="0" cellpadding="2"><tr><td><font color="{1}"><b>{0}</b></font></td></tr></table>>;'.format(label, color))
        print("]")


class SetOfProcesses(Process):
    def __init__(self, name, **kwargs):
        super().__init__(name, **kwargs)

    def dfd(self, **kwargs):
        self._is_drawn = True
        color = _setColor(self)
        label = _setLabel(self)
        print("{0} [\n\tshape = doublecircle;\n\tcolor = {1};\n".format(self._uniq_name(), color))
        print('\tlabel = <<table border="0" cellborder="0" cellpadding="2"><tr><td><font color="{1}"><b>{0}</b></font></td></tr></table>>;'.format(label, color))
        print("]")


class Dataflow(Element):
    source = varElement(None)
    sink = varElement(None)
    isResponse = varBool(False)
    response = varElement(None)
    responseTo = varElement(None)
    srcPort = varInt(-1)
    dstPort = varInt(-1)
    isEncrypted = varBool(False)
    protocol = varString("")
    data = varString("")
    authenticatedWith = varBool(False)
    order = varInt(-1)
    implementsCommunicationProtocol = varBool(False)
    name = varString("")
    note = varString("")
    usesVPN = varBool(False)
    authorizesSource = varBool(False)
    usesSessionTokens = varBool(False)
    usesLatestTLSversion = varBool(False)

    def __init__(self, source, sink, name, **kwargs):
        self.source = source
        self.sink = sink
        super().__init__(name, **kwargs)

    def __set__(self, instance, value):
        print("Should not have gotten here.")

    def dfd(self, mergeResponses=False, **kwargs):
        self._is_drawn = True
        color = _setColor(self)
        label = _setLabel(self)
        if self.order >= 0:
            label = '({0}) {1}'.format(self.order, label)
        direction = "forward"
        if mergeResponses and self.response is not None:
            direction = "both"
            resp_label = _setLabel(self.response)
            if self.response.order >= 0:
                resp_label = "({0}) {1}".format(self.response.order, resp_label)
            label += "<br/>" + resp_label
        print("\t{0} -> {1} [\n\t\tcolor = {2};\n\t\tdir = {3};\n".format(
            self.source._uniq_name(),
            self.sink._uniq_name(),
            color,
            direction,
        ))
        print('\t\tlabel = <<table border="0" cellborder="0" cellpadding="2"><tr><td><font color="{1}"><b>{0}</b></font></td></tr></table>>;'.format(label, color))
        print("\t]")


class Boundary(Element):
    elements = varElements()

    def __init__(self, name, **kwargs):
        super().__init__(name, **kwargs)

    def dfd(self):
        if self._is_drawn:
            return

        self._is_drawn = True
        logger.debug("Now drawing boundary " + self.name)
        label = self.name
        print("subgraph cluster_{0} {{\n\tgraph [\n\t\tfontsize = 10;\n\t\tfontcolor = firebrick2;\n\t\tstyle = dashed;\n\t\tcolor = firebrick2;\n\t\tlabel = <<i>{1}</i>>;\n\t]\n".format(self._uniq_name(), label))
        for e in self.elements:
            if e._is_drawn:
                continue
            # The content to draw can include Boundary objects
            logger.debug("Now drawing content {}".format(e.name))
            e.dfd()
        print("\n}\n")


def get_args():
    _parser = argparse.ArgumentParser()
    _parser.add_argument('--debug', action='store_true', help='print debug messages')
    _parser.add_argument('--dfd', action='store_true', help='output DFD')
    _parser.add_argument('--report', help='output report using the named template file (sample template file is under docs/template.md)')
    _parser.add_argument('--exclude', help='specify threat IDs to be ignored')
    _parser.add_argument('--seq', action='store_true', help='output sequential diagram')
    _parser.add_argument('--list', action='store_true', help='list all available threats')
    _parser.add_argument('--describe', help='describe the properties available for a given element')

    _args = _parser.parse_args()
    return _args
