use std::collections::HashSet;

use crate::{BoogieInstruction, loop_headers};

pub fn boogie_to_string(instructions: &[BoogieInstruction]) -> String {
    let mut code = String::new();

    let loop_header_idx = loop_headers(instructions);
    let backward_branch_targets: HashSet<_> = loop_header_idx
        .iter()
        .copied()
        .map(|i| match &instructions[i] {
            BoogieInstruction::Label(name) => name.clone(),
            _ => unreachable!(),
        })
        .collect();

    for instr in instructions {
        match instr {
            BoogieInstruction::Label(name) => {
                code.push_str(&format!("{}:\n", name));

                if backward_branch_targets.contains(name) {
                    code.push_str("    assert last_store < old(step);\n");
                    code.push_str("    assert step >= old(step);\n");
                    code.push_str("    assert (forall i : int, e : Effect :: old(step) <= i && i < step && effects[i] == e ==> ! (is_write(e)));\n\n");
                }
            }
            BoogieInstruction::Instr(name, out, ops) => {
                code.push_str(&format!(
                    "    call {} := execute({}({}));\n",
                    out,
                    name,
                    ops.join(",")
                ));
            }
            BoogieInstruction::Branch(target, condition) => {
                code.push_str(&format!("    if ({}) {{ goto {}; }}\n", condition, &target,));
            }
            BoogieInstruction::Jump(target) => {
                code.push_str(&format!("    goto {};\n", target));
            }
            BoogieInstruction::Return => {
                code.push_str("    return;\n");
            }
            BoogieInstruction::Unhandled(ins) => {
                code.push_str(&format!("    // Unhandled: {}\n", ins));
            }
        }
    }
    code
}
