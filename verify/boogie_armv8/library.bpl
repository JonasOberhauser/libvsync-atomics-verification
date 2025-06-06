datatype Flags {
    Flags (
        N: bool,
        Z: bool,
        C: bool
    )
}

datatype Ordering {
    AcquirePC(),
    Acquire(),
    Release(),
    Fence(mode : FenceType),
    NoOrd()
}

datatype Monitor {
    exclusive(addr: int),
    open()
}

var local_monitor: Monitor;
var flags: Flags;
var monitor_exclusive: bool;
var event_register: bool;

datatype FenceType {
    SY(),
    LD()
}

datatype Instruction {
    ld(acq: bool, addr: int, mask: int),
    ldx(acq: bool, addr: int, mask: int),
    st(rel: bool, src, addr: int),
    stx(rel: bool, src, addr: int),

    csel(src1, src2: int, cond: bool),
    mov(src: int),
    cmp(opnd1, opnd2: int),
    add(first, second: int),
    sub(first, second: int),
    andd(first, second: int),
    orr(first, second: int),
    eor(first, second: int),
    wfe(),
    sevl(),

    dmb(mode : FenceType),
    //LSE instructions

    mvn(src: int), // complements the bits in result
    neg(src: int), // negates the bits in the result
    
    swp(acq, rel: bool, src, addr: int, mask: int), // exchanges 
    cas(acq, rel: bool, exp, src, addr: int, mask: int), // compare and swap

    ldumax(acq, rel: bool, src, addr: int, mask: int), // maximum between src register, and loaded value
    ldclr(acq, rel: bool, src, addr: int, mask: int), // bitwise and between src and ~loaded value
    ldset(acq, rel: bool, src, addr: int, mask: int), // bitwise or between  src and loaded value
    ldeor(acq, rel: bool, src, addr: int, mask: int), // bitwise xor between src and loaded value
    ldadd(acq, rel: bool, src, addr: int, mask: int), // sum of src and loaded value

    stumax(rel: bool, src, addr: int), // store maximum between src and addr
    stclr(rel: bool, src, addr: int), // store and between src and ~addr
    stset(rel: bool, src, addr: int), // store or
    steor(rel: bool, src, addr: int), // store xor
    stadd(rel: bool, src, addr: int) // store sum
}

function returning_load(instr : Instruction) : bool {
    instr is ld
    || instr is ldx
    || instr is swp
    || instr is cas 
    || instr is ldumax
    || instr is ldclr
    || instr is ldset
    || instr is ldeor
    || instr is ldadd
}

/* Prove meta properties about execute, that are used in the proof */
procedure verify_execute(instr : Instruction) returns (r : int)
    modifies flags, step, local_monitor, monitor_exclusive, event_register, last_load, last_store;

    requires (instr is stx ==> local_monitor is exclusive && local_monitor->addr == instr->addr);
    requires instr is wfe ==> event_register || monitor_exclusive;


    ensures {:msg "load return is correct"} (
            forall a, v: int, vis : bool :: 
                effects[old(step)] == read(a,v,vis) && returning_load(instr)  ==> 
                    r == v
    );

    requires last_load < step;
    requires last_store < step;
    ensures {:msg "last_load tracked correctly"} (
            (is_read(effects[old(step)])) ==
                (old(step) == last_load)
    );
    ensures ( // can define no_writes through last_store 
            (is_write(effects[old(step)])) ==
                (old(step) == last_store)
    );
    ensures last_load < step;
    ensures last_store < step;

    requires (forall i, j : int :: atomic[i, j] ==> i <= j && j < step);
    ensures (forall i : int ::
            atomic[i, old(step)] ==> i == last_load && old(step) == last_store
        );
    ensures (forall i, j : int ::
            atomic[i, j] ==> i <= j && j < step);

    ensures step == old(step) + 1;
{
    call r := execute(instr);
}

function visible(instr : Instruction) : bool {
    ! (instr is stumax
    || instr is stclr
    || instr is stset
    || instr is steor
    || instr is stadd)
}

function updated_value(instr: Instruction, read_value : int) : int {
    if instr is cas || instr is swp
    then instr->src
    else if instr is ldclr || instr is stclr
    then and[instr->src, read_value]
    else if instr is ldset || instr is stset
    then or[instr->src, read_value]
    else if instr is ldeor || instr is steor
    then xor[instr->src, read_value] 
    else if instr is ldumax || instr is stumax
    then max[instr->src, read_value]
    else if instr is ldadd || instr is stadd
    then instr->src + read_value
    else 0
}

function rmw(instr: Instruction) : bool {
    instr is swp
    || instr is ldumax
    || instr is stumax
    || instr is ldclr
    || instr is stclr
    || instr is ldset
    || instr is stset
    || instr is ldeor
    || instr is steor
    || instr is ldadd
    || instr is stadd
}

function reads(instr: Instruction) : bool {
    rmw(instr) || instr is ld || instr is ldx || instr is cas
}

function writes(instr: Instruction) : bool {
    rmw(instr) || instr is st
}

procedure execute(instr: Instruction) returns (r : int);
    modifies flags, step, local_monitor, monitor_exclusive, event_register, last_load, last_store;
    ensures step == old(step + 1);
    ensures {:msg "state"} (
        var stx_success, cas_success :=
            old(local_monitor == exclusive(instr->addr)
            && monitor_exclusive),
            r == instr->exp;
        (r == if instr is stx then b2i(! stx_success)
            else if instr is mov then instr->src
            else if instr is add then instr->first + instr->second
            else if instr is sub then instr->first - instr->second
            else if instr is andd then bit_and(instr->first, instr->second)
            else if instr is orr  then bit_or (instr->first, instr->second)
            else if instr is eor  then bit_xor(instr->first, instr->second)
            else if instr is mvn  then bit_not(instr->src)
            else if instr is neg  then 0 - instr->src
            else if instr is csel then if instr->cond then instr->src1 else instr->src2
            else if returning_load(instr) then bit_and(r, instr->mask)
            else r)
        &&
        (last_load == if reads(instr)
                    then
                        old(step)
                    else
                        old(last_load))
        &&
        (last_store == if writes(instr) || rmw(instr)
                        || (instr is cas && cas_success)
                        || (instr is stx && stx_success)
                    then
                        old(step)
                    else
                        old(last_store))
        &&
        (local_monitor == if instr is ldx then exclusive(instr->addr)
                        else if instr is stx 
                            || instr is cas
                            || reads(instr) || writes(instr)
                            || instr is wfe
                        then open()
                        else old(local_monitor))
        &&
        (flags == if instr is cmp
                then (
                    var diff := instr->opnd1 - instr->opnd2;
                    Flags(diff < 0, diff == 0, diff >= 0)
                )
                else
                    old(flags)
                )
        &&
        (effects[old(step)] == 
                        if rmw(instr)
                        || (instr is cas && cas_success)
                        then update(instr->addr, r, visible(instr), updated_value(instr, r))
                        else if writes(instr) || (instr is stx && stx_success)
                        then write(instr->addr, instr->src)
                        else if reads(instr)
                        then read(instr->addr, r, visible(instr))
                        else no_effect() 
            )
        &&
        (ordering[old(step)] == if instr->acq && reads(instr)
                    then Acquire()
                    else if instr->rel && (writes(instr)
                            || (instr is stx && stx_success)
                            || (instr is cas && cas_success))
                    then Release()
                    else if instr is dmb
                    then Fence(instr->mode)
                    else NoOrd())
        &&
        (atomic[last_load, old(step)] == (rmw(instr) || (instr is stx && stx_success) || (instr is cas && cas_success)))
        &&
        (   // external write can clear monitor at any moment. has to set event register.
            (monitor_exclusive == false && event_register == old(monitor_exclusive || event_register))
            || monitor_exclusive == if instr is ldx then true
                else if writes(instr)
                    || instr is stx 
                    || (instr is cas && cas_success)
                then false
                else old(monitor_exclusive))
        &&
        /* D1.6.1 The Event Register
            The Event Register for a PE is set by any of the following:
            • A Send Event instruction, SEV, executed by any PE in the system.
            • A Send Event Local instruction, SEVL, executed by the PE.
            • An exception return.
            • The clearing of the global monitor for the PE.
            • An event from a Generic Timer event stream, see Event streams on page D11-5991.
            • An event sent by some IMPLEMENTATION DEFINED mechanism.


            NOTE: since we only care about proving that the event register is set upon reaching wfe, we just allow it to become set non-deterministically.
            But it can be cleared only by wfe.
        */
        (old(event_register) ==> (event_register || instr is wfe))
        &&
        (step == old(step) + 1)
    );
    requires {:msg "either event register or global monitor is set for WFE"}
        instr is wfe ==> event_register || monitor_exclusive;
    requires {:msg "stx is paired to ldx"}
        instr is stx ==> local_monitor == exclusive(instr->addr);


function cbnz(test: int): bool {
    test != 0
}

function cbz(test: int): bool {
    test == 0
}

// C1.2.4 Condition code
datatype ConditionCode {
    EQ(), // Equal
    NE(), // Not equal
    HS(), // Unsigned higher or same
    LO(), // Unsigned lower
    HI(), // Unsigned higher
    LS()  // Unsigned lower or same
}

function branch(cond: ConditionCode, flags: Flags): bool {(
    var N, Z, C := flags->N, flags->Z, flags->C;
         if cond is EQ then Z
    else if cond is NE then !Z
    else if cond is HS then C
    else if cond is LO then !C
    else if cond is HI then C && !Z
    else if cond is LS then !(C && !Z)
    else false // Should never be reached
)}


function ppo(step1, step2: StateIndex, ordering: [StateIndex] Ordering, effects: [StateIndex] Effect): bool {
    step1 < step2 && (
        // Barrier-ordered-before
        ordering[step1] is Acquire ||
        ordering[step1] is AcquirePC ||
        ordering[step2] is Release ||
        (ordering[step1] is Release && ordering[step2] is Acquire) ||
        (exists f : int :: step1 < f && f < step2 && ordering[f] == Fence(SY())) ||
        (exists f, a, v : int :: step1 < f && f < step2 && ordering[f] == Fence(LD())
            && effects[step1] == read(a,v,true))
    )
}


function is_sc(order: Ordering): bool {
    order is Acquire || order is Release
}