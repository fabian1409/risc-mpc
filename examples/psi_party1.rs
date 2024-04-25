use risc_mpc::{
    PartyBuilder, Register, Result, Share, TcpChannel, Value, CMP_AND_TRIPLES, PARTY_1, U64_BYTES,
};
use std::collections::BTreeSet;

fn main() -> Result<()> {
    env_logger::init();

    // https://godbolt.org/z/zjcPTzr8W
    let program = "
        psi:
                li      a6, 0
                li      a7, 0
                li      t1, 0
        .LBB0_1:
                slli    t0, a7, 3
                add     t0, t0, a2
                slli    t2, t1, 3
                add     t2, t2, a0
        .LBB0_2:
                sltu    t3, a7, a3
                sltu    a5, t1, a1
                and     a5, a5, t3
                beqz    a5, .LBB0_8
                ld      t3, 0(t2)
                ld      a5, 0(t0)
                bgeu    t3, a5, .LBB0_5
                addi    t1, t1, 1
                addi    t2, t2, 8
                j       .LBB0_2
        .LBB0_5:
                bgeu    a5, t3, .LBB0_7
                addi    a7, a7, 1
                j       .LBB0_1
        .LBB0_7:
                addi    t1, t1, 1
                addi    a7, a7, 1
                slli    a5, a6, 3
                add     a5, a5, a4
                sd      t3, 0(a5)
                addi    a6, a6, 1
                j       .LBB0_1
        .LBB0_8:
                mv      a0, a6
                ret
    "
    .parse()?;

    let set = BTreeSet::from([3, 4, 5]);
    let k = set.len() as u64;
    let n = k;

    let ch = TcpChannel::new(PARTY_1, "127.0.0.1:8000".parse().unwrap())?;
    let mut party = PartyBuilder::new(PARTY_1, ch)
        .register(Register::x10, Value::Public(0x0)) // set0 address
        .register(Register::x11, Value::Public(n)) // set0 length
        .register(Register::x12, Value::Public(U64_BYTES * n)) // set1 address
        .register(Register::x13, Value::Public(k)) // set1 length
        .register(Register::x14, Value::Public(U64_BYTES * (n + k))) // intersection address
        .address_range(
            U64_BYTES * n,
            set.iter()
                .map(|x| Value::Secret(Share::Arithmetic(*x)))
                .collect(),
        )?
        .n_and_triples(CMP_AND_TRIPLES * 2 * (n + k)) // 2 lt per set element cmp
        .build()?;

    party.execute(&program)?;

    let len = party.register(Register::x10)?;
    let intersection =
        party.address_range(U64_BYTES * (n + k)..U64_BYTES * (n + k) + U64_BYTES * len)?;

    println!("intersection = {intersection:?}");
    Ok(())
}
