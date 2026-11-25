# Third-party notices

This source snapshot retains eight attributed public supporting declarations adapted from existing public proof sources. They are included within the 1052 counted supporting declarations and are not claimed as newly authored proofs. Additional retained private Lean helpers receive credit below and add no exported proof count. Here, private helper refers to Lean declaration visibility, not permission to disclose someone else's private platform content.

## Scope of licensing

The Apache License 2.0 text in `LICENSES/Apache-2.0.txt` accompanies the third-party portions described here. It is not a blanket license grant for the original portions of this snapshot. Copyright and other rights in original portions remain with their respective holders; this release does not add a new license for those portions.

The Prove2Me public-contribution terms, effective September 24, 2026 at 15:55 UTC, apply Apache 2.0 to public contributions made after that time, to the extent contributors own or can license them. These retained dependencies were obtained from the public library and their recorded contribution dates are after that effective time. The terms exclude private content and do not override other third-party rights. See https://prove2.me/terms (checked November 24, 2026).

The OpenAI math release additionally specifies Apache 2.0: https://github.com/openai/math/blob/main/LICENSE . The retained cube/Gaussian material is attributed to result family 117 at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a` and to its accepted public Prove2Me source contributor, dbenbenn.

## Eight attributed public declarations

The theorem and submission identifiers below identify public source records, not the private verification jobs for this project.

1. `BMCompactReuse.lintegral_minkowski` in `RootReusedLp.lean`. Contributor: Mazecto. Public theorem: `86a95b04-e229-44a5-b876-7b0c566f0c41`; accepted public source submission: `1e4d48fc-52a0-454e-b81b-127598801b95`.

2. `BMCompactReuse.integral_minkowski` in `RootReusedLp.lean`. Contributor: Mazecto. Public theorem: `d0310cdf-e1f8-4290-9f6d-306a7175260d`; accepted public source submission: `b9da12cb-7228-4e0c-9ec0-b6f5ea7e9903`.

3. `BMCompactReuse.scalar_convolution_contraction` in `RootReusedLp.lean`. Contributor: Mazecto. Public theorem: `be569d3f-b16b-4b19-8f28-ebccb1a76a43`; accepted public source submission: `560f5d0c-4b6a-4130-9809-c9afbbe5b783`.

4. `BMCompactGradientReuse.classical_translation_norm_bound` in `GradientAnalyticBatch.lean`. Contributor: Mazecto. Public theorem: `67d0148b-a528-4693-828c-f09c3e47e04f`; accepted public source submission: `7bc58d37-b255-400f-887c-78f3ef050334`.

5. `OAI.UniformSparsestCut.CubePoincare.uniform_cube_first_moment_oai` in `ContinuousCubePoincare.lean`. Contributor: dbenbenn. Public theorem: `dc48791a-5c97-41dd-a18f-06499967b692`; accepted public source submission: `9609744e-dfd2-43f4-ae55-546e6ea5325a`.

6. `BMCompactGradientHessian.exists_l2_directional_derivative_of_local_quotient_bound` in `GradientHessianExtraction.lean`. Contributor: sometik179 (Hunter converse); Lazyfill (private pairing prerequisite). Public theorem: `13300b40-c9bb-4c66-b1b1-22f4017c0539`; accepted public source submission: `fcca92bd-0710-45e1-8717-932d87045928`.

7. `BMCompactMorreyReuse.morrey_increment_of_contDiff` in `UpstreamMorreyEstimate.lean`. Contributor: Mazecto. Public theorem: `a4ec1d80-8bd0-4c9f-a46b-5dc84f79a245`; accepted public source submission: `9751a637-a770-45a4-bbc4-675023e631b0`.

8. `BMCompactPDE.exists_actual_global_morrey_constant` in `UpstreamMorreyRepresentative.lean`. Contributor: Mazecto (adapted WeakMorrey and private AE-selection method). Public theorem: `786bedb8-e687-4d6e-800a-09794ca50991`; accepted public source submission: `0a92530c-1c20-49f0-b083-6ff1698e5223`.

## Adaptations and retained helper credits

- **Mazecto, mixed-norm Minkowski and convolution:** `RootReusedLp.lean` incorporates the three listed existing proof bodies. Platform imports were replaced by actual preceding proof bodies; exported declarations and dependency references were renamed while retaining their mathematics. The first two results are derived mixed-norm generalizations using Holder/Tonelli or Jensen, with mathematical background from John K. Hunter's *Notes on Partial Differential Equations* (2014), rather than verbatim Hunter statements. The scalar normalized-kernel convolution bound uses the same Minkowski averaging method.
- **Mazecto, translations:** `GradientAnalyticBatch.lean` localizes the existing classical translation-norm estimate by adjusting native imports, namespace and helper visibility. It is an attributed existing proof, not new authorship.
- **dbenbenn and the OpenAI math release, cube and Gaussian estimates:** `ContinuousCubePoincare.lean` retains the public cube proof and a Gaussian prerequisite whose helpers and alias have private Lean visibility. The public Gaussian theorem is `6b7f1162-9bc5-4e50-8b0d-d6a7b0e2a146`, submission `7ab58e87-98d5-4664-b0f4-1fef9b2fad33`. Only needed definition sections are retained; proof bodies are unchanged. Imports use actual pinned Mathlib sources, and helper visibility is localized. The Gaussian prerequisite adds no exported proof count.
- **sometik179 and Lazyfill, weak derivative extraction:** `GradientHessianExtraction.lean` adapts sometik179's regional test-space/Hahn-Banach/Riesz extraction argument and Lazyfill's convolution quotient-pairing limit. Lazyfill's public theorem is `93835bcb-bdbc-4706-adbe-19b48ce839be`, accepted source submission `587eb193-a9a9-4b91-b93a-66890dd3c53a`. Native scalar tests and explicit Frechet directional derivatives replace platform-specific interfaces; private retained proof bodies add no additional exports. The original Hunter H2 theorem is not claimed to be newly checked or integrated wholesale.
- **Mazecto, Morrey estimates and representatives:** `UpstreamMorreyEstimate.lean` and `UpstreamMorreyRepresentative.lean` adapt the public smooth Morrey-increment proof, WeakMorrey method, and dense almost-everywhere selection method. Native Sobolev approximation and weak-gradient interfaces are constructed in the project adaptation; the imported methods and helpers remain credited. Private prerequisites add no extra exported proof count.

## Other dependencies

Mathlib is obtained separately at the pinned revision in `lake-manifest.json`; it is not vendored in this snapshot. Mathlib and its fetched dependencies retain their own licenses and notices. Lean retains its own license. Imported declarations are not claimed as original contributions of this project.

All existing attribution comments in the Lean sources are retained. This file provides the public source attribution omitted when private platform receipts, failed attempts, caches and internal provenance payloads were left out of the public snapshot.
