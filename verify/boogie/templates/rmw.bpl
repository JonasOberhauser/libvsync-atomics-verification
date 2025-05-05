var #registers: int;

/*
    op          - operation to be performed
*/

procedure rmw (op: RMWOp)
    modifies step, last_load, last_store, #state, #registers;
    
    ensures {:msg "if no write happened, the value from memory is already the result of operation"} (
        var address, input1, input2 := old(#address), old(#input1), old(#input2);
        no_writes(old(step), step, last_store) ==>
            (
                var extracted := bit_and(extract_value(address - effects[last_load]->addr, effects[last_load]->read_value), #value_mask);
                extracted == op[extracted, input1, input2]
            )
        );
    ensures {:msg "atomicity"}
        !no_writes(old(step), step, last_store) ==> (
            atomic[last_load, last_store]
        );
    ensures {:msg "store produces write to correct address with correct value"}
        !no_writes(old(step), step, last_store) ==> (
            var address, input1, input2 := old(#address), old(#input1), old(#input2);
            (var extracted := bit_and(extract_value(address - effects[last_load]->addr, effects[last_load]->read_value), #value_mask);
                effects[last_store]->write_value == 
                        align_value(address - effects[last_store]->addr, 
                            bit_and(op[extracted, input1, input2], #value_mask),
                            effects[last_load]->read_value,
                            #value_mask)
                    )
        );
{
    #implementation
}