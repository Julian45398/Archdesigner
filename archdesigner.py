''' Simple example that shows how to execute a command on a small model developed in EMF.
This example was used to teach EOQ basics to students.

2024 Bjoern Annighoefer
'''

from eoq3.domain import *
from eoq3.error import *
from eoq3.value import *
from eoq3.command import *
from eoq3.query import *
from eoq3.concepts import *
from eoq3.logger import ConsoleLogger, DEFAULT_LOGGER_LEVELS
from eoq3.util.eoqfile import *
from eoq3.serializer import TextSerializer
from eoq3utils import *
from eoq3pyecoreutils import *
from eoq3pyecoreutils.loadecorefile import *
from eoq3pyecoreutils.saveecorefile import *

from pyecore import *

def routeSignal(domain, m1model, archModel, signal):
    signalRoute = domain.Do(Crt("*M1OBJECT", 1, ['SignalRoute', m1model, 'signalRoute']))
    res = domain.Do(Cmp().Set(signalRoute, 'signal', signal[3]).Add(archModel, 'signalRoutes', signalRoute))
    startEndDevices = domain.Do(Get(Qry(archModel).Pth('taskAssignments*').Zip([
                        Sel(Pth('task').Equ(signal[1])), #srcDevice
                        Sel(Pth('task').Equ(signal[2])) #dstDevice
                    ]).Pth('device')))[0]


    # if signal stays in the same device just add a single segment with the device bound
    if (startEndDevices[0] == startEndDevices[1]):
        res = domain.Do(Cmp().Crt("*M1OBJECT", 1, ['RouteSegment', m1model, 'deviceSegment'])
                .Set(His(-1), 'device', startEndDevices[0])
                .Add(signalRoute, 'segments', His(0)))
        return

    # else use dijkstras algorithm:
    unvisited = [device for device in domain.Do(Get(Qry(archModel).Pth('devices*')))]
    visited = []
    current = startEndDevices[0]
    nodeData = {node: [2147483647, None] for node in unvisited}
    nodeData[current][0] = 0
    distanceWalked = I32(0)

    while True:
        connections = domain.Do(Get(Qry(archModel).Pth('connections*').Sel(Pth('start').Equ(current)).Zip([
            Pth('name'),
            Pth('length'), #path length
            Pth('start'), #start device
            Pth('end') #end device
        ])))
        smallest = 2147483647 
        nextNode = current
        for connection in connections:
            if connection[3] in visited:
                continue
            if connection[1] < smallest:
                smallest = connection[1]
                nextNode = connection[3]
            if distanceWalked+connection[1] < nodeData[connection[3]][0]:
                nodeData[connection[3]] = [distanceWalked + connection[1], current] # update distance and previous node
        distanceWalked += smallest
        visited.append(current)
        unvisited.remove(current)
        if nextNode == startEndDevices[1]:
            nodeData[nextNode] = [distanceWalked, current]
            break
        current = nextNode
    #reconstruction of the shortest path:
    current = startEndDevices[1]
    while True:
        data = nodeData[current]
        connection = domain.Do(Get(Qry(archModel).Pth('connections*')
                                    .Sel(Pth('start').Equ(data[1]))
                                    .Sel(Pth('end').Equ(current))))[0]
        #create route segment for device and used connection
        res = domain.Do(Cmp().Crt("*M1OBJECT", 1, ['RouteSegment', m1model, 'deviceSegment'])
                            .Set(His(-1), 'device', current)
                            .Add(signalRoute, 'segments', His(0))
                            .Crt("*M1OBJECT", 1, ['RouteSegment', m1model, 'connectionSegment'])
                            .Set(His(-1), 'connection', connection)
                            .Add(signalRoute, 'segments', His(3)))
        current = data[1]
        if current == startEndDevices[0]:
            #add start device route segment:
            res = domain.Do(Cmp().Crt("*M1OBJECT", 1, ['RouteSegment', m1model, 'deviceSegment'])
                            .Set(His(-1), 'device', current)
                            .Add(signalRoute, 'segments', His(0)))
            break
    segments = domain.Do(Get(Qry(signalRoute).Pth('segments').Zip([
        Pth('device').Trm().Pth('name'),
        Pth('connection').Trm().Pth('name')
    ])))
    print("Route signal segments: ", segments)

def routeSignals(domain, m1model):
    archModels = domain.Do(Get(Qry(m1model).Pth('*MODELROOT').Cls('ArchModel')))

    for archModel in archModels:
        signals = domain.Do(Get(Qry(archModel).Pth('signals*').Zip([
                Pth('name'),
                Pth('src'), #src task
                Pth('dst'), #dst task
                Qry()
        ])))
        
        for signal in signals:
            routeSignal(domain, m1model, archModel, signal)
     
    print("signals routed...")

def addConstraints(domain, m2model):
    ser = TextSerializer()

    #signals must have different src and dst tasks
    signalClass = domain.Do(Get(Qry(m2model).Pth(M2PACKAGE.CLASSES)
                                .Sel(Pth(M2CLASS.NAME).Equ('Signal')).Idx(0)))
    signalConstraint = ser.SerQry(Pth('src').Neq(Pth('dst')))
    domain.Do(Crt(CONCEPTS.MXCONSTRAINT, 1, [signalClass, signalConstraint]))

    #connections must have different start and end devices
    connectionClass = domain.Do(Get(Qry(m2model).Pth(M2PACKAGE.CLASSES)
                                    .Sel(Pth(M2CLASS.NAME).Equ('Connection')).Idx(0)))
    connectionConstraint = ser.SerQry(Pth('start').Neq(Pth('end')))
    domain.Do(Crt(CONCEPTS.MXCONSTRAINT, 1, [connectionClass, connectionConstraint]))

    #segments must have a reference either to a device or a connection but cannot have both!
    segmentClass = domain.Do(Get(Qry(m2model).Pth(M2PACKAGE.CLASSES)
                                 .Sel(Pth(M2CLASS.NAME).Equ('RouteSegment')).Idx(0)))
    segmentConstraint = ser.SerQry(Pth('device').Neq(None).Add(Pth('connection').Equ(None))
                                   .Sub(Pth('device').Equ(None).Add(Pth('connection').Neq(None))))
    domain.Do(Crt(CONCEPTS.MXCONSTRAINT, 1, [segmentClass, segmentConstraint]))

    print("constraints added!")

def verifyModel(domain, m1model):
    archModels = domain.Do(Get(Qry(m1model).Pth('*MODELROOT').Cls('ArchModel')))

    for archModel in archModels:
        signals = domain.Do(Get(Qry(archModel).Pth('signals*')))
        res = domain.Do(Ver(signals))
        print("signal results: ", res)

        connections = domain.Do(Get(Qry(archModel).Pth('connections*')))
        res = domain.Do(Ver(connections))
        print("connection results: ", res)
        
        signalSegments = domain.Do(Get(Qry(archModel).Pth('signalRoutes*').Pth('segments*')))
        for segments in signalSegments:

            res = domain.Do(Ver(segments))
        print("segment results: ", res)
    print("model verified")

def createExampleUserModel(domain, m2model):
    m1model = domain.Do(Crt("*M1MODEL", 1, [m2model, "usermodel"]))
    #Instantiating all Objects and connections:
    archModel = domain.Do(Crt("*M1OBJECT", 1, ['ArchModel', m1model, 'archmodel'])) #0
    res = domain.Do(Cmp()
                    #Tasks:
                    .Crt("*M1OBJECT", 2, ['Task', m1model, 'tasks']) #1
                        .Set(His(-1), 'name', ['Task1', 'Task2']) #2
                        .Add(archModel, 'tasks', His(-2)) #3
                    #Signal:
                    .Crt("*M1OBJECT", 1, ['Signal', m1model, 'Signal12']) #4
                        .Set(His(-1), ['name', 'src', 'dst'], ['Signal12', His(0).Idx(0), His(0).Idx(1)]) #5
                        .Add(archModel, 'signals', His(-2)) #6
                    #Devices:
                    .Crt("*M1OBJECT", 4, ['Device', m1model, 'devices']) #7
                        .Set(His(-1), 'name', ['Device1', 'Device2', 'Device3', 'Device4']) #8
                        .Add(archModel, 'devices', His(-2)) #9
                    #TaskAssignments:
                    .Crt("*M1OBJECT", 2, ['TaskAssignment', m1model, 'taskAssignments']) #10
                        .Set(His(-1), ['task', 'device'], [[His(0).Idx(0), His(6).Idx(0)],
                                                            [His(0).Idx(1), His(6).Idx(3)]]) #11
                        .Add(archModel, 'taskAssignments', His(-2)) #12
                    #Connections:
                    .Crt("*M1OBJECT", 4, ['Connection', m1model, 'connections']) #13
                        .Set(His(-1), ['name', 'length', 'start', 'end'], [['Con12', 3, His(6).Idx(0), His(6).Idx(1)], 
                                                                            ['Con13', 1, His(6).Idx(0), His(6).Idx(2)],
                                                                            ['Con24', 4, His(6).Idx(1), His(6).Idx(3)],
                                                                            ['Con34', 2, His(6).Idx(2), His(6).Idx(3)]]) #14
                        .Add(archModel, 'connections', His(-2))) #15

    return m1model




if "__main__" == __name__:
    metafile = "model/archdesigner.ecore"

    logger = ConsoleLogger(activeLevels=DEFAULT_LOGGER_LEVELS.L1_ERROR)

    domain = CreateDomain(DOMAIN_TYPES.LOCAL, {logger})

    try:
        LoadEcoreFile(metafile, domain)
        m2model = domain.Do(Get(Pth('*M2MODEL').Idx(0)))
        addConstraints(domain, m2model)

        m1model = createExampleUserModel(domain, m2model)
        print("routing signals...")
        routeSignals(domain, m1model)

        verifyModel(domain, m1model)

        SaveEcoreFile('model/example.archdesigner', m1model, domain, metafile=metafile)
    finally:
        CleanUpDomain(domain)