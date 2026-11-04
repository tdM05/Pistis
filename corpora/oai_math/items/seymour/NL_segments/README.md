# the goal of this
segment NL so we fully undersatnd the proof. Adding custom visuals in parts when needed etc.

The paper is at (/u/taddmao/code/autoform/math/preprints/A-proof-of-Seymours-second-neighborhood-conjecture-September-23-2026/paper.pdf)

# Motivation
Why am I doing this?
Segmenting the sections, and labelling these sections, allows us to allows us to understand the implicit structure this NL document contains; such as if I am in a particular lemma, for which overall section is this lemma for, or like what are the relationships, like who uses this lemma (could have like an edge), or why this matters etc.
This also seperates what is "high-level" that really points to other things, and what is "the actual proof" meaning the low-level actual steps, that the high level uses.

# output
First most important thing is to agree on a good way to store data. viz is after

then for viz, ideally we can see exactly the pdf, and it shoudl be quite intuitive navigating, seeing the sections, maybe having a bird's eye view mode etc. just something that is easy to seee these sections. Ideally also for these sections, we can have like diagrams of graphs, showcasing what these things mean on the side, kinda like info cards.

## potential future extension for math undersnatding of new ai results (very relevant now)
an interesting idea, is maybe we can have a model query this proof/graph, and some small llm could tell us or point and answer quesitons about this specific proof in the future: what depends on what, the high level, visualizing this, where it points to in the formal, how everything connects with visuals etc.