module Base
{}

module Utils
{}

module BackwardConnections
{
    import opened Base
    import opened Utils

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

    function CombineCircuits(c1: Circuit, c2: Circuit): (r: Circuit)
        requires Wellformed(c1)
        requires Wellformed(c2)
    {}

    predicate IsEquivalentCircuit(node_is_member: nat->bool, node_map: nat-->nat, c1: Circuit, c2: Circuit)
        requires forall inp :: inp in c1.backconns && node_is_member(inp.node_id) ==> node_is_member(c1.backconns[inp].node_id)
        requires forall n :: node_is_member(n) ==> node_map.requires(n)
    {}

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
            IsEquivalentCircuit(a=>true, a=>a, c1, r) &&
            IsEquivalentCircuit(a=>a < offset, a=>a, r, c1)
    {
    }

    lemma CombineCircuitsCorrect(c1: Circuit, c2: Circuit, r: Circuit)
        requires Wellformed(c1)
        requires Wellformed(c2)
        requires r_is_result: r == CombineCircuits(c1, c2)
        ensures
            var offset := |c1.nodes|;
            IsEquivalentCircuit(a=>true, a=>a, c1, r) &&
            IsEquivalentCircuit(a=>a < offset, a=>a, r, c1) &&

            IsEquivalentCircuit(a=>true, a=>a+offset, c2, r) &&

            true
    {}
}