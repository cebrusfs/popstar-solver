import re

with open("popstar_solver/src/bin/arena.rs", "r") as f:
    arena = f.read()

# For NRPA commit: remove BmctsAgent
arena_nrpa = re.sub(r'struct BmctsAgent \{.*?\n\}\n', '', arena, flags=re.DOTALL)
arena_nrpa = re.sub(r'impl Agent for BmctsAgent \{.*?\n\}\n', '', arena_nrpa, flags=re.DOTALL)
arena_nrpa = arena_nrpa.replace("    let bmcts_agent = BmctsAgent { beam_width: 100, rollout_count: 20 };\n", "")
arena_nrpa = arena_nrpa.replace("        &bmcts_agent,\n", "")

with open("popstar_solver/src/bin/arena.rs", "w") as f:
    f.write(arena_nrpa)
