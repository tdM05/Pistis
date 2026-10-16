# Document faithfulness

## Proof faithfulness (starting from NL)

### Motivating example
This comes in parts
1. segment the NL text into "proof steps", which are a type of segment, and align these.
2. For each proof step, segment further using faithalign to get atomic components, and align these

**Why two levels of segmentation? They do the same thing in some sense**
There is no good reason why 2 specifically. why not 3, why not 1. The issue with 1, is that if you try and be too fine grained, and you are for example, doing faithfulness over entire textbook, aligning a single "x" to a specific lean part, it is very difficult to know *which* x this is, what it means, etc and usually it needs some kind of local context.

What about three? Let's say hypothetically you are formalizing the entire internet. It would be a good idea to start by segmenting into parts, where you categorize by genre, like Academic papers, entertainment, job-realted, etc., then in like the papers category, you may want to do fields like AI, math, bio, chem, etc., and within these there are papers by different authors etc., then in a single paper there are multiple sections, in sections some are proofs, and in profs there may be faith-align type of granularity. The point is, *for human understanding*, we may need may levels, depending on size, which ultimately is a hyperparmeter meant to optimze human-understanding.

## Proposal
Therefore, it makes sense to talk about $K$-Pistis, Pistis extended to $K$ categories.

I want to emphasize that the goal of this framework is for *humans to understand whether a formal document matches an NL document*. It does *not* on its own assert faithfulness, nor on its own assert correctness of proof. Precisely, *this framework makes it easier for humans to check formal document matches NL document*, and if a human checks each part, then together with the human(s), we claim it is faithful. We take the problem away from "get human to just verify the entire thing at once" to automating everything we can, and human only checks what is necessary and makes it easier for human.

$K$-Pistis has a roote $s$, top level segments $s_1, ..., s_n$, second level $s_{i, 1}, ..., s_{i, n_i}$ for each $s_i$, and so on until we get a tree of depth $K$ (at the end one of the segments is $s_{i_1, i_2, ..., i_K}$). Each of these $s$ is a string.

Also each level has a category: $C_1, ..., C_K$. For example in this paper we could have $C_1=\text{paper section}$, $C_2=\text{proof step}$, $C_3=\text{faithalign labels}$.

1. **Coverage**. For any node $s$, the direct children of it concatenate exactly to $s$
2. **Atomicity**. each $s$ is a single thing in their category. For example, a single ting at the proof step level is "a single assertion, with assumption set." We assume an oracle can judge this soundly
3. "Atomic Faithfulness". Each $s$ is indeed faithful. Again assme oracle can judge this soundly
4. Per-category condition. Different categories may have their own conditions
5. Soundness -- well the formal proof compiles in Lean obviously.