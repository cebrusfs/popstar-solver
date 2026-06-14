import re

with open('src/bin/arena.rs', 'r') as f:
    content = f.read()

arena_setup = """    let agents: Vec<Box<dyn Agent>> = vec![
        Box::new(RolloutBeamSearchAgent {
            name: "RolloutBeam-W2000".to_string(),
            beam_width: 2000,
        }),
        Box::new(UltimateMetaAgent {
            name: "UltimateMeta-W1000".to_string(),
            beam_width: 1000,
        }),
    ];"""

content = re.sub(r'let agents: Vec<Box<dyn Agent>> = vec!\[.*?\];', arena_setup, content, flags=re.DOTALL)

with open('src/bin/arena.rs', 'w') as f:
    f.write(content)
