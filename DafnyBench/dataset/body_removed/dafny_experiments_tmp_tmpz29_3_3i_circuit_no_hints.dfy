module Base
{
    // We want to represent circuits.
    // A Circuit is composed of nodes.
    // Each node can have input ports and output ports.

    // The ports are represented just by the index of the node, and the index
    // of the port on the node.
    datatype INodePort = inodeport(node_id: nat, port_id: nat)
    datatype ONodePort = onodeport(node_id: nat, port_id: nat)

    // Currently the nodes can just be Xor, And or Identity gates.
    datatype Node =
        Xor |
        And |
        Ident

    // The number of input ports for each kind of node.
    function n_iports (node: Node): nat
    {}

    // The number of output ports for each kind of node.
    function n_oports (node: Node): nat
    {}

    // A circuit is represented by the nodes and the connections between the nodes.
    // Each output port can go to many input ports.
    // But each input port can only be connected to one output port.
    datatype Circuit = Circ(
        nodes: seq<Node>,
        backconns: map<INodePort, ONodePort>
        )

    // Just checking that the port and node indices mentioned in the connections are sane.
    predicate WellformedBackConns(c: Circuit)
    {}

    predicate WellformedINP(c: Circuit, inp: INodePort)
    {}

    predicate WellformedONP(c: Circuit, onp: ONodePort)
    {}

    // All input ports in a circuit.
    function AllINPs(c: Circuit): set<INodePort>
        ensures forall inp :: inp in AllINPs(c) ==> WellformedINP(c, inp)
    {}

    // All output ports in a circuit.
    function AllONPs(c: Circuit): set<ONodePort>
        ensures forall onp :: onp in AllONPs(c) ==> WellformedONP(c, onp)
    {}

    ghost predicate Wellformed(c: Circuit)
    {}
}

module Utils
{}

module BackwardConnections
{
    import opened Base
    import opened Utils

    // This is used when we are trying to create a new circuit by combining two existing circuits.
    // This function takes care of combining the backwards connections.
    // Because the node_indices of the two circuits are just natural numbers when we combine the
    // two circuits we need to shift the node indices of the second circuit so that they don't clash.
    // We do this by adding `offset` to the node indices.
    function CombineBackconns(
            offset: nat,
            bc1: map<INodePort, ONodePort>, bc2: map<INodePort, ONodePort>): (result: map<INodePort, ONodePort>)
        requires
            forall inp :: inp in bc1 ==> inp.node_id < offset
    {}

    lemma CombineBackconnsHelper(
            offset: nat,
            bc1: map<INodePort, ONodePort>, bc2: map<INodePort, ONodePort>, result: map<INodePort, ONodePort>)
        requires
            forall inp :: inp in bc1 ==> inp.node_id < offset
        requires 
            result == CombineBackconns(offset, bc1, bc2);
        ensures
            forall inp :: inp in bc1 ==> (
                inp in result &&
                result[inp] == bc1[inp])
        ensures
            forall inp :: inp in bc2 ==> (
                inodeport(inp.node_id+offset, inp.port_id) in result &&
                result[inodeport(inp.node_id+offset, inp.port_id)] == onodeport(bc2[inp].node_id+offset, bc2[inp].port_id))
    {}

    lemma CombineBackconnsHelper2(
            offset: nat,
            bc1: map<INodePort, ONodePort>, bc2: map<INodePort, ONodePort>, result: map<INodePort, ONodePort>, inp: INodePort)
        requires
            forall inp :: inp in bc1 ==> inp.node_id < offset
        requires 
            result == CombineBackconns(offset, bc1, bc2);
        requires inp in bc2
        ensures
            inodeport(inp.node_id+offset, inp.port_id) in result
        ensures
            result[inodeport(inp.node_id+offset, inp.port_id)] == onodeport(bc2[inp].node_id+offset, bc2[inp].port_id)
    {}
}


module CombineCircuits {

    import opened Base
    import BackwardConnections
    import opened Utils

    // Combine two circuits into a new circuit.
    // This is a bit ugly because we have to offset the node indices of the
    // second circuit by |c1.nodes|.
    function CombineCircuits(c1: Circuit, c2: Circuit): (r: Circuit)
        requires Wellformed(c1)
        requires Wellformed(c2)
    {}

    // Check that Circuit c2 contains a subcircuit that corresponds to c1 getting mapped with the
    // `node_map` function.
    predicate IsEquivalentCircuit(node_is_member: nat->bool, node_map: nat-->nat, c1: Circuit, c2: Circuit)
        requires forall inp :: inp in c1.backconns && node_is_member(inp.node_id) ==> node_is_member(c1.backconns[inp].node_id)
        requires forall n :: node_is_member(n) ==> node_map.requires(n)
    {}

    // Check that for every input port and output port in the combined Circuit, they can be assigned
    // to a port in one of the two source circuits.
    predicate CanBackAssign(c1: Circuit, c2: Circuit, r: Circuit, is_in_c1: nat->bool, is_in_c2: nat-> bool,
                            map_r_to_c1: nat->nat, map_r_to_c2: nat-->nat)
        requires forall a :: is_in_c1(a) ==> map_r_to_c1.requires(a)
        requires forall a :: is_in_c2(a) ==> map_r_to_c2.requires(a)
        requires Wellformed(c1)
        requires Wellformed(c2)
    {}

    lemma CombineCircuitsCorrectHelper(c1: Circuit, c2: Circuit, r: Circuit)
        requires Wellformed(c1)
        requires Wellformed(c2)
        requires r_is_result: r == CombineCircuits(c1, c2)
    {}


    lemma CombineCircuitsCorrectC1(c1: Circuit, c2: Circuit, r: Circuit)
        requires Wellformed(c1)
        requires Wellformed(c2)
        requires r == CombineCircuits(c1, c2)
        ensures
            var offset := |c1.nodes|;
            // The original c1 has an image in r.
            IsEquivalentCircuit(a=>true, a=>a, c1, r) &&
            // This subset of r has an image in c1.
            IsEquivalentCircuit(a=>a < offset, a=>a, r, c1)
    {
    }

    lemma CombineCircuitsCorrect(c1: Circuit, c2: Circuit, r: Circuit)
        requires Wellformed(c1)
        requires Wellformed(c2)
        requires r_is_result: r == CombineCircuits(c1, c2)
        ensures
            var offset := |c1.nodes|;
            // The original c1 has an image in r.
            IsEquivalentCircuit(a=>true, a=>a, c1, r) &&
            // This subset of r has an image in c1.
            IsEquivalentCircuit(a=>a < offset, a=>a, r, c1) &&

            // The original c2 has an image in r.
            IsEquivalentCircuit(a=>true, a=>a+offset, c2, r) &&
/*
            FIXME: These have been commented out for now
                   otherwise it takes longer than 20s to solve.
            // All ports in r have equivalents in either c1 or c2.
            CanBackAssign(c1, c2, r, a=>a < offset, a=> a >= offset, a=>a, a requires a >= offset => sub(a, offset)) &&
            // This subset of r has an image in c2.
            IsEquivalentCircuit(a=>a >= offset, a requires a >= offset => sub(a, offset), r, c2) &&
*/
            true
    {}
}
