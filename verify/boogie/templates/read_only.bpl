var #registers: int;

procedure read_only()
    modifies step, atomic, last_load, last_store, #state, #registers;
    ensures no_writes(old(step), step, last_store);
    ensures {:msg "produced read effects are correct"}
        old(step) <= last_load && last_load < step ==> effects[last_load] == read(old(#address), #output, true);
{
    #implementation
}