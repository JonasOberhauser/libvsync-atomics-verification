var #registers: int;

/*
    store_order - ordering of store
*/
procedure write(store_order: OrderRelation)
    modifies step, effects, ordering, atomic, last_load, last_store, #state, #registers;
    ensures {:msg "no other writes"}
        (forall i : StateIndex ::
            old(step) <= i && i < step && (exists e : Effect :: effects[i][e] && (e is write))
                ==> i == last_store);
    ensures {:msg "store ordering"}
        !no_writes(old(step), step, last_store)
            ==> store_order[last_store, old(step), step, ordering, effects];
{
    #implementation
}

