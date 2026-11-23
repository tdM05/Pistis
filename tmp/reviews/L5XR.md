We thank the reviewer for the thoughtful review and concrete suggestions, and are glad they found the direction promising.

**Overall.** Our goal is to use theoretical guarantees to be precise about why we expect certain environment families to scale, and then to test this empirically. As the reviewer notes, the three sufficient conditions are not directly actionable on their own. This is why we introduce interest and capability breadths: they connect the conditions to task structure that can be inspected, and Figure 2 tests the resulting prediction.

**F0: Section 5.2**
We will shorten Section 5.2 to focus on its connection to the structural properties.

**F1: Contribution beyond the conditions**
Our contribution is to connect the conditions to task structure (Section 5.1). Under Assumption 5.1, fixed capability and interest breadths bound the number of relevant agents independently of system size (Condition 1). They also motivate bounded individual approximation error (Condition 3), which remains a hypothesis. This identifies a family with a structural basis for expecting scalability, and a prediction to test empirically.

**F2: Actionability**
While the three conditions are difficult to control directly, interest and capability breadths, which Section 5.1 connects to them, are parameters we *do* control: the designer chooses which task types each agent can complete and how task rewards are assigned.

**F3: Experimental evaluation**
Figure 2 shows that keeping both interest and capability constant better preserves performance, with some decline at 41 agents.
If even one of interest or capability is not constant, decentralized performance degrades as the number of agents increases over the tested range.
The centralized comparison also degrades in the IC-constant case.

**F4: Suggestions (i) and (ii)**
For (i), estimating breadths from a few episodes is a natural next step and would help flag promising environment families, though it would not by itself verify Conditions 2 and 3. For (ii), Section 5.3 already provides a concrete algorithmic direction: aggregate values only from relevant agents. With a correctly identified relevant set, this preserves greedy action selection under exact values, and Conditions 1 and 3 suffice for relevant scalability without Condition 2. Learning these sets is an open problem, with partial reward decoupling [5, 11] offering a starting point. We view both suggestions as valuable extensions of this structural analysis.
