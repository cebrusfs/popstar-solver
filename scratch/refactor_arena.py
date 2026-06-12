import re

with open("popstar_solver/src/bin/arena.rs", "r") as f:
    content = f.read()

# Replace struct BeamSearchAgent
struct_old = """struct BeamSearchAgent {
    beam_width: usize,
}"""
struct_new = """struct BeamSearchAgent {
    name: String,
    beam_width: usize,
    heuristic: fn(&Board) -> i32,
}"""
content = content.replace(struct_old, struct_new)

# Replace fn name
name_old = """    fn name(&self) -> &str {
        "BeamSearch"
    }"""
name_new = """    fn name(&self) -> &str {
        &self.name
    }"""
content = content.replace(name_old, name_new)

# Replace heuristic call
heuristic_old = """            unique_vec.sort_by_cached_key(|(b, s)| {
                let h = calculate_predictive_heuristic(b);
                -(s + h)
            });"""
heuristic_new = """            unique_vec.sort_by_cached_key(|(b, s)| {
                let h = (self.heuristic)(b);
                -(s + h)
            });"""
content = content.replace(heuristic_old, heuristic_new)

# Remove old BeamSearchAgentW500 and W5000
remove_pattern = re.compile(r"struct BeamSearchAgentW500 \{.*?\}\n\nstruct BeamSearchAgentW5000 \{.*?\}\n\n", re.DOTALL)
content = remove_pattern.sub("", content)

# Modify main instantiations
main_old = """    let beam_agent_50 = BeamSearchAgent { beam_width: 50 };
    let beam_agent_500 = BeamSearchAgentW500 { beam_width: 500 };
    let beam_agent_5000 = BeamSearchAgentW5000 { beam_width: 5000 };"""

main_new = """    let beam_agent_50 = BeamSearchAgent { name: "BeamSearch-W50-V2".to_string(), beam_width: 50, heuristic: calculate_predictive_heuristic };
    let beam_agent_500 = BeamSearchAgent { name: "BeamSearch-W500-V2".to_string(), beam_width: 500, heuristic: calculate_predictive_heuristic };
    let beam_agent_5000 = BeamSearchAgent { name: "BeamSearch-W5000-V2".to_string(), beam_width: 5000, heuristic: calculate_predictive_heuristic };"""
content = content.replace(main_old, main_new)

with open("popstar_solver/src/bin/arena.rs", "w") as f:
    f.write(content)
