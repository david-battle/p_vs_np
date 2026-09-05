Recommendation
Work on the bounded-arithmetic (un)provability of complexity lower bounds — the program of §8.2 — specifically the "reverse mathematics of lower bounds" line (Krajíček → Razborov → Pich–Santhanam 2021 → Li–Oliveira 2023 → Chen–Li–Oliveira, FOCS 2024).
This is the one direction in the notes where the independence intuition (§4–§5) becomes a tractable, unconditional theorem, rather than a hypothesis about ZFC that §3 argues is almost certainly false in the interesting sense.
Why this direction
1. It is the notes' own conclusion, made concrete. §8's verdict is that self-reference attaches to the proof space, not the sentence. The theories PV₁ / S¹₂ / APC₁ are exactly where "ZFC ⊬" becomes "PV ⊬" and consistency-strength arguments become proof-complexity arguments (p_vs_np_notes.md:396-402). Pich–Santhanam's mechanism is literally the §8.2 "hardness hides its own proof" structure: provability of the lower bound implies its falsity (witnessing extracts an algorithm), so unprovability follows from soundness — unconditionally. That is the GEB rhyme as a rigorous theorem, and the field is now actively extending it.
2. The field is hot, young, and has stated open problems. Chen–Li–Oliveira (2024) ends with explicit targets that don't require a career's worth of machinery:
- Does PV₁ prove the nondeterministic time hierarchy theorem? If not, what principle is it equivalent to?
- Is near-cubic formula lower bound for Andreev's function equivalent over PV₁ to a variant of the weak witnessing pigeonhole principle?
- Multi-round communication lower bounds from WPHP_WIT(PV)?
- "Find equivalences between your favorite lower bound statement and a combinatorial principle" — an open invitation.
Their headline result (the classic Ω(n²) Palindrome lower bound is unprovable in APC₁ under a crypto assumption) shows that elementary, textbook lower bounds still have unknown proof-theoretic status. This is unusual: publishable results are available on simple objects.
3. It directly connects the two firmest anchors in §6/§8. Liu–Pass (OWFs ⇔ K^t hardness) and Razborov's PRG-conditional unprovability are both crypto-to-logic bridges. The unprovability results in CLO24 are conditioned on cryptographic assumptions; meta-complexity is the natural tool to weaken or remove those conditions. Someone who holds both threads (§6's meta-complexity and §8.2's bounded arithmetic) is positioned to do something the specialists in either camp aren't.
4. The "hardness axioms" observation in §4 is now a research thesis. CLO24's abstract literally says "complexity lower bounds can be formally seen as fundamental mathematical axioms with far-reaching implications" — your §4 correction (P≠NP ⊂ ETH ⊂ SETH as an extrinsically-justified tower) is the informal version of what they're proving formally over PV₁. There is room for a paper that takes the foundational framing seriously: which lower bounds are "axioms" (independent, non-derivable from weaker ones) versus theorems, in the reverse-mathematics sense.
Concrete entry points, ordered by effort
- Reverse-mathematics classification of a specific lower bound (e.g., the NTIME hierarchy, or a specific formula/branching-program bound): find the principle over PV₁ it is equivalent to. Self-contained, publishable at a logic or complexity venue, pattern already established.
- Sharpen a conditional unprovability to unconditional, or trade the crypto assumption for a meta-complexity one (Liu–Pass style). Higher payoff, higher risk.
- The §8.3 bridge: Pudlák's finite consistency statements Con_T(n) and the Krajíček–Pudlák optimal-proof-system connection. Slower-moving subfield, but it is where "budget" self-reference is exactly right and where a new idea from the foundations side could matter.
Why not the other directions in the notes
- Independence from ZFC (§3, §5): Ben-David–Halevi makes the truth-but-independent case carry an "almost polynomial SAT" signature nothing supports; nobody expects progress and there's no technique. Not publishable as more than a survey.
- Large cardinals deciding P vs NP (§2 caveat): genuinely open, zero handle.
- The hashing chain (§6): closes a loop P≠NP ⇒ P=NP; Valiant–Vazirani runs the other way. Its honest descendant is meta-complexity, which the recommendation absorbs.
- Machine-Gödel / §8.1 construction: folklore-shaped and near-tautological by the notes' own analysis (§7). An exercise, not a paper.
- Direct lower bounds / new techniques: the correct long-run goal, but unpublishable for anyone not already deep in circuit complexity, and the barriers (§5) apply in full.
Caveats
- I'm recommending a field, not a theorem. Publishable progress still requires choosing one of the open problems above and mastering Krajíček's Proof Complexity (2019) and Buss/KPT witnessing. Budget several months of reading.
- The community is small but very strong (Krajíček, Pich, Santhanam, Oliveira, Chen, Li, Hirahara). The advantage of an outsider here is the foundational framing (§4) and the meta-complexity bridge (§6), not raw technique.
- Details I state from memory (exact theories, exact statements of Razborov 1995) should be verified against the sources; the CLO24 and PS21 abstracts above are from the papers themselves.
