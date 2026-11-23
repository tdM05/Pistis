We thank the reviewer for their thoughtful feedback and for recognizing the importance of the problem and the value of our structural perspective.

**W1. Connection to theory.**
Under Assumption 5.1, fixed breadths bound the number of relevant agents independently of system size, establishing Condition 1. They also limit the tasks each agent can perform and benefit from. This motivates our hypothesis that the information needed to predict individual returns remains limited as the system grows, making bounded individual approximation error (Condition 3) plausible. Condition 2 remains open for full aggregation. Section 5.3 shows that Conditions 1 and 3 suffice for relevant scalability (Definition 5.2) when aggregation is restricted to a correctly identified relevant set.

**W2. Single environment.**
Our controlled environment lets us vary both breadths independently as system size grows, directly testing the proposed structural hypothesis. Figure 2 supports the predicted distinction between the both-constant and growing-breadth regimes. We acknowledge that evaluation in additional domains is needed to establish the generality of this empirical finding.

**Q1. Information requirements and scope.**
Our scalability claim concerns bounded aggregate value-approximation error under the stated information assumptions.

**Individual rewards.** Each agent learns from its own reward signal. This fits systems with task-specific feedback, as motivated by the separate benchmark objectives in the Hugging Face example (Section 5.2).

**Global state.** Shared state can be available in software-agent systems with a common workspace, while full observability is restrictive in swarms and wireless networks. Fixed breadths motivate the hypothesis that limited state information may suffice to predict individual returns (Section 5.1).

**Value estimates.** Full aggregation incurs growing communication requirements. Section 5.3 shows that exact values from relevant agents suffice to preserve greedy action selection, since all other agents contribute equally across actions. The relevant-set size is bounded under Condition 1, and partial reward decoupling [5, 11] offers a starting point for learning these sets.

While our framework does not establish scalability under partial observations and constrained communication, it identifies structural reasons why limited information may suffice and outlines concrete directions for relaxing these assumptions.
