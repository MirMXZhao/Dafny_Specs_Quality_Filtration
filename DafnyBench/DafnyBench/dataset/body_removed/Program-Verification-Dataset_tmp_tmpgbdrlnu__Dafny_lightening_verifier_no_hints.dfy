class CrashableMem<T> {
    var mem_ : array<T>;
    method read(off : int) returns (r : T)
        requires 0 <= off < mem_.Length;
    {}

    method write(off : int, val : T)
        requires 0 <= off < mem_.Length;
        modifies mem_;
    {}
}

datatype GhostState = GS(
    num_entry : int,
    log : seq<int>,

    mem_len : int,
    mem : seq<int>,
    old_mem : seq<int>,
    ideal_mem : seq<int>,
    countdown : int,
    first_log_pos : map<int, int>
)

datatype GhostOp = WriteMem(off : int, val : int)
                 | WriteLog(off : int, val : int)
predicate ghost_state_inv(s : GhostState) {}

function init_ghost_state(log : seq<int>, mem : seq<int>, countdown : int) : GhostState
    requires |log| > 0;
    requires countdown >= 0;
    ensures ghost_state_inv(init_ghost_state(log, mem, countdown));
{}

function mem_write(s : GhostState, off: int, val: int) : GhostState
    requires ghost_state_inv(s);
    requires 0 <= off < s.mem_len;
    ensures ghost_state_inv(mem_write(s, off, val));
{}

function log_write(s : GhostState, off : int, val: int) : GhostState
    requires ghost_state_inv(s);
    requires 0 <= off < |s.log|;
    ensures ghost_state_inv(log_write(s, off, val));
{}

predicate valid_op(s : GhostState, op : GhostOp)
{}

function countdown (s : GhostState) : GhostState
{}

function normal_step (s : GhostState, op : GhostOp) : GhostState
    requires valid_op(s, op);
    requires ghost_state_inv(s);
    ensures ghost_state_inv(normal_step(s, op));
{}

function ghost_step (s : GhostState, op : GhostOp) : (GhostState, bool)
    requires valid_op(s, op);
    requires ghost_state_inv(s);
    ensures ghost_state_inv(normal_step(s, op));
{}

function mem_write_step (s : GhostState, off : int, val : int) : (GhostState, bool)
    requires 0 <= off < s.mem_len;
    requires ghost_state_inv(s);
{}

function log_write_step (s : GhostState, off : int, val : int) : (GhostState, bool)
    requires 0 <= off < |s.log|;
    requires ghost_state_inv(s);
{}

function set_num_entry (s : GhostState, n : int) : (GhostState, bool)
    requires 0 <= n * 2 < |s.log|;
{}

predicate crashed (s : GhostState)
{}

predicate old_mem_equiv (s : GhostState)
    requires ghost_state_inv(s);
{}

predicate ghost_tx_inv (s : GhostState)
{}

function ghost_begin_tx (s : GhostState) : GhostState
    requires ghost_state_inv(s);
    requires s.num_entry == 0;
    ensures ghost_state_inv(ghost_begin_tx(s));
    ensures ghost_tx_inv(ghost_begin_tx(s));
    ensures old_mem_equiv(ghost_begin_tx(s));
{}

function ghost_commit_tx (s : GhostState) : (GhostState, bool)
    requires ghost_tx_inv(s);
    requires old_mem_equiv(s);
    ensures ghost_state_inv(ghost_commit_tx(s).0);
    ensures ghost_tx_inv(ghost_commit_tx(s).0);
    ensures !ghost_commit_tx(s).1 ==> old_mem_equiv(ghost_commit_tx(s).0);
    ensures ghost_commit_tx(s).1 ==> ghost_commit_tx(s).0.num_entry == 0;
{}

function ghost_tx_write (s0 : GhostState, off : int, val : int) : GhostState
    requires ghost_tx_inv(s0);
    requires old_mem_equiv(s0);
    requires 0 <= off < s0.mem_len;
    requires 0 <= s0.num_entry * 2 + 2 < |s0.log|;
    ensures ghost_tx_inv(ghost_tx_write(s0, off, val));
    ensures old_mem_equiv(ghost_tx_write(s0, off, val));
    ensures |ghost_tx_write(s0, off, val).mem| == s0.mem_len;
    ensures !crashed(ghost_tx_write(s0, off, val)) ==> ghost_tx_write(s0, off, val).mem[off] == val;
{}

function reverse_recovery (s0 : GhostState, idx : int) : GhostState
    requires ghost_tx_inv(s0);
    requires old_mem_equiv(s0);
    requires 0 <= idx <= s0.num_entry;
    ensures ghost_tx_inv(reverse_recovery(s0, idx));
    ensures old_mem_equiv(reverse_recovery(s0, idx));
    ensures s0.old_mem == reverse_recovery(s0, idx).old_mem;
    ensures s0.first_log_pos == reverse_recovery(s0, idx).first_log_pos;
    ensures forall o :: o in s0.first_log_pos && s0.first_log_pos[o] >= idx ==>
                reverse_recovery(s0, idx).mem[o] == s0.mem[o];
    ensures forall o :: o in s0.first_log_pos && 0 <= s0.first_log_pos[o] < idx ==>
                reverse_recovery(s0, idx).mem[o] == s0.old_mem[o];
{}

function ghost_recover (s0 : GhostState) : GhostState
    requires ghost_tx_inv(s0);
    requires old_mem_equiv(s0);
    ensures ghost_recover(s0).mem == s0.old_mem;
    ensures ghost_recover(s0).num_entry == 0;
{}


class UndoLog {
    var log_ : array<int>;
    var mem_ : array<int>;

    var impl_countdown : int;
    ghost var gs : GhostState;

    constructor () {}

    predicate ghost_state_equiv(gs : GhostState)
        reads this;
        reads mem_;
        reads log_;
    {}
    predicate state_inv()
        reads this;
        reads log_;
    {}

    method init(log_size : int, mem_size : int, countdown : int)
        requires log_size > 1;
        requires mem_size > 0;
        requires log_size < 0xffffffff;
        modifies this;
        ensures fresh(log_);
        ensures fresh(mem_);
        ensures state_inv();
        ensures ghost_state_equiv(gs);
    {}

    method impl_countdown_dec()
        modifies this;
        requires impl_countdown > 0;
        requires mem_ != log_;
        ensures mem_ != log_;
        ensures impl_countdown == old(impl_countdown) - 1;
        ensures impl_countdown >= 0;
        ensures gs == old(gs);
        ensures log_[..] == old(log_)[..];
        ensures mem_[..] == old(mem_)[..];
    {}

    method write_mem(off : int, val : int)
        modifies this;
        modifies mem_;
        requires 0 <= off < mem_.Length;
        requires mem_ != log_;
        requires ghost_state_inv(gs);
        requires ghost_state_equiv(gs);
        requires 0 <= off < gs.mem_len;
        ensures mem_ == old(mem_);
        ensures log_ == old(log_);
        ensures gs == old(gs);
        ensures ghost_state_equiv(mem_write_step(gs, off, val).0);
    {}

    method write_log(off : int, val : int)
        modifies this;
        modifies log_;
        requires 0 <= off <= |gs.log|;
        requires mem_ != log_;
        requires ghost_state_inv(gs);
        requires ghost_state_equiv(gs);
        requires off == 0 ==> 0 <= val * 2 < |gs.log|;
        ensures mem_ != log_;
        ensures mem_ == old(mem_);
        ensures log_ == old(log_);
        ensures log_.Length == old(log_).Length;
        ensures mem_[..] == old(mem_)[..];
        ensures log_[off] == val || log_[off] == old(log_)[off];
        ensures forall i :: 0 <= i < log_.Length && i != off ==> log_[i] == old(log_)[i];
        ensures gs == old(gs);
        ensures off > 0 ==> ghost_state_equiv(log_write_step(gs, off - 1, val).0);
        ensures off == 0 ==> ghost_state_equiv(set_num_entry(gs, val).0);
    {}

    method begin_tx()
        modifies log_;
        modifies this;
        requires state_inv();
        requires ghost_state_equiv(gs);
        requires ghost_state_inv(gs);
        requires log_[0] == 0;
        ensures mem_ == old(mem_);
        ensures log_ == old(log_);
        ensures state_inv();
        ensures ghost_state_equiv(gs);
        ensures ghost_tx_inv(gs);
    {}

    method commit_tx()
        modifies log_;
        modifies this;
        requires state_inv();
        requires ghost_state_equiv(gs);
        requires ghost_state_inv(gs);
        requires ghost_tx_inv(gs);
        requires old_mem_equiv(gs);
        ensures mem_ == old(mem_);
        ensures log_ == old(log_);
        ensures ghost_state_equiv(gs);
        ensures state_inv();
    {}

    method tx_write(offset: int, val : int)
        modifies this;
        modifies log_;
        modifies mem_;
        requires state_inv();
        requires mem_ != log_;
        requires 0 <= offset < mem_.Length;
        requires ghost_state_equiv(gs);
        requires ghost_tx_inv(gs);
        requires old_mem_equiv(gs);
        requires 0 <= log_[0] * 2 + 3 < log_.Length;
        ensures ghost_state_equiv(gs);
        ensures ghost_tx_inv(gs);
        ensures old_mem_equiv(gs);
    {}

    // we assume that recover won't crash (though this code works when recover can fail)
    method recover()
        modifies log_;
        modifies mem_;
        modifies this;
        requires state_inv();
        requires ghost_tx_inv(gs);
        requires old_mem_equiv(gs);
        requires ghost_state_equiv(gs);
        ensures gs == ghost_recover(old(gs));
        ensures ghost_state_equiv(gs);
    {}
}

lemma crash_safe_single_tx(init_log : seq<int>, init_mem : seq<int>,
                           countdown : int,
                           writes : seq<(int, int)>)
    requires |init_log| > 0;
    requires countdown >= 0;
    requires forall i :: 0 <= i < |writes| ==>
                0 <= writes[i].0 < |init_mem|;
    requires 0 < |writes| * 2 < |init_log|;
{}
