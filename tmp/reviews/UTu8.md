We thank the reviewer for their thoughtful feedback and for recognizing the relevance of our question, the experimental design, and the promising results.

**W1. Additional seeds.** We added two seeds per point in Figure 2 (five total). Below: mean normalized performance ± SD.

| N | Centralized: both bounded | Decentralized: both bounded | Decentralized: interest bounded | Decentralized: capability bounded |
|---:|---:|---:|---:|---:|
| 11 | 95.23 ± 2.97 | 68.09 ± 9.69 | 68.09 ± 9.69 | 68.09 ± 9.69 |
| 21 | 69.72 ± 3.75 | 71.25 ± 4.55 | 67.28 ± 25.60 | 48.49 ± 5.55 |
| 31 | 59.13 ± 4.80 | 76.27 ± 4.64 | 65.63 ± 17.56 | 45.77 ± 2.30 |
| 41 | 37.86 ± 17.71 | 57.23 ± 1.84 | 44.60 ± 3.83 | 42.92 ± 3.96 |

The main trend persists: decentralized learning with both breadths bounded preserves performance best as N grows. We will report ten seeds per point in the camera-ready.

**W2. Reward distribution.** The increase is intentional. Motivated by human societies and the Hugging Face example, we model settings where more agents caring about a task can increase variation in its collective value. Total task rewards sum individual rewards from $B_I$ interested agents, giving SD $\sqrt{B_I}\sigma_a$. We study increasing interest breadth under this additive reward model, including the associated reward variation.

**W3. Computational resources.** We fixed network width and scaled total training steps with system size to keep steps per agent constant. Parameters per agent nevertheless grew from 7,545 at 11 agents to 25,417 at 41 agents (Appendix, Table 5). We will state these controls directly in the Introduction and remove the claim that fixed width is a proxy for bounded per-agent computational resources.

**W4. Hugging Face example.** This illustrates the breadths, rather than providing evidence of scalability. *Interest:* agents formed groups around shared tasks and benefited from their outcomes, but not other groups' tasks. *Capability:* agents divided labor within groups, contributing to particular tasks (e.g., findings or exploit payloads). This pattern motivates studying decentralized scaling in systems with limited interests and capabilities. We will clarify this framing.
