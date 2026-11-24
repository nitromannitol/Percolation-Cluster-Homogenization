import PercolationClusterHomogenization.Proofs.Percolation.PlanarStripFlip
import PercolationClusterHomogenization.Proofs.Percolation.PlanarResampleStopping

/-!
# Flipping one bond changes the meshed cubes only near it

Let `ω, ω'` be configurations of `ℤ²` equal off a bond `e = {x, y}` and let the partition exist
for `ω`, with partition cube `□_𝒫(x)` of side `s`. The square of side `s` around `x` is one of the
squares tested in the strip mesh of `□_𝒫(x)`, so its four outer strips of width `⌊s/100⌋` have open
crossings, which do not use `e`. By the flip lemma (`crossing_iff_of_flip`, and its version for
top-bottom crossings `vcrossing_iff_of_flip`, obtained by exchanging the coordinates), the strip
meshes of width at least `s + 2` are the same for `ω` and `ω'` (`planarMesh_iff_of_flip`). A cube
whose square of side `9 × side` does not contain `e` has the same meshes by locality. Hence the
meshed cubes of `ω` and `ω'` agree except for cubes of side below `101 s` whose square of side
`9 × side` contains `x` (`meshedFlipBound_of_flip`).
-/

open LatticeProb.Percolation Rigidity.Proofs.Section5

namespace Rigidity.Percolation

open Percolation.Literature.LatticeModels (Site zdGraph)

/-! ### The exchange of the coordinates acting on configurations -/

theorem swapIso_symm_apply (x : Vertex 2) : swapIso.symm x = siteSwap x := by
  funext i
  simp [Rigidity.Proofs.S3.signedPermIso, Rigidity.Proofs.S3.signedPermVertex, siteSwap,
    Equiv.symm_swap]

theorem siteSwap_mem_latticeBox {c v : Site 2} {m n : ℕ} (hv : v ∈ latticeBox c m n) :
    siteSwap v ∈ latticeBox (siteSwap c) n m := by
  simp only [latticeBox, Set.mem_setOf_eq, siteSwap_zero, siteSwap_one] at hv ⊢
  omega

theorem siteSwap_siteSwap (z : Site 2) : siteSwap (siteSwap z) = z := by
  funext i
  fin_cases i <;> simp

/-- Open walks are carried to open walks of the configuration with exchanged coordinates. -/
theorem reachIn_swap_box {ω : Configuration 2} {c a b : Site 2} {m n : ℕ}
    (h : ReachIn ω (latticeBox c m n) a b) :
    ReachIn (Rigidity.Proofs.S3.configurationMap swapIso ω) (latticeBox (siteSwap c) n m)
      (siteSwap a) (siteSwap b) := by
  obtain ⟨W, hW⟩ := h
  refine ⟨(W.map (Rigidity.Proofs.S3.openGraphMap swapIso ω).toRelEmbedding.toRelHom).copy
    (swapIso_apply a) (swapIso_apply b), fun v hv => ?_⟩
  rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map, List.mem_map] at hv
  obtain ⟨u, hu, rfl⟩ := hv
  change swapIso u ∈ _
  rw [swapIso_apply]
  exact siteSwap_mem_latticeBox (hW u hu)

/-- Open walks of the configuration with exchanged coordinates come from open walks. -/
theorem reachIn_unswap_box {ω : Configuration 2} {c a b : Site 2} {m n : ℕ}
    (h : ReachIn (Rigidity.Proofs.S3.configurationMap swapIso ω) (latticeBox (siteSwap c) n m)
      a b) :
    ReachIn ω (latticeBox c m n) (siteSwap a) (siteSwap b) := by
  obtain ⟨W, hW⟩ := h
  refine ⟨(W.map (Rigidity.Proofs.S3.openGraphMap swapIso ω).symm.toRelEmbedding.toRelHom).copy
    (swapIso_symm_apply a) (swapIso_symm_apply b), fun v hv => ?_⟩
  rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map, List.mem_map] at hv
  obtain ⟨u, hu, rfl⟩ := hv
  change swapIso.symm u ∈ _
  rw [swapIso_symm_apply]
  have := siteSwap_mem_latticeBox (hW u hu)
  rwa [siteSwap_siteSwap] at this

theorem configurationMap_swap_agree_off {ω ω' : Configuration 2} {e : Bond 2}
    (hagree : ∀ b, b ≠ e → ω' b = ω b) :
    ∀ b, b ≠ Rigidity.Proofs.S3.bondMap swapIso e →
      Rigidity.Proofs.S3.configurationMap swapIso ω' b =
        Rigidity.Proofs.S3.configurationMap swapIso ω b := by
  intro b hb
  obtain ⟨b₀, rfl⟩ := (Rigidity.Proofs.S3.bondMap swapIso).surjective b
  rw [Rigidity.Proofs.S3.configurationMap_apply_bondMap,
    Rigidity.Proofs.S3.configurationMap_apply_bondMap]
  exact hagree b₀ fun h => hb (h ▸ rfl)

theorem bondMap_swap_val {e : Bond 2} {x y : Vertex 2} (hexy : e.1 = s(x, y)) :
    (Rigidity.Proofs.S3.bondMap swapIso e).1 = s(siteSwap x, siteSwap y) := by
  change Sym2.map swapIso e.1 = _
  rw [hexy, Sym2.map_mk, swapIso_apply, swapIso_apply]

/-! ### The flip lemma for left-right and top-bottom crossings -/

/-- **The flip lemma for left-right crossings.** -/
theorem crossing_iff_of_flip {ω ω' : Configuration 2} {e : Bond 2}
    (hagree : ∀ b, b ≠ e → ω' b = ω b) {x y : Vertex 2} (hexy : e.1 = s(x, y))
    {c₀ : Site 2} {M w : ℕ}
    (hT : ∃ a b, ReachIn ω (latticeBox ![c₀ 0, c₀ 1 + M - w] M w) a b ∧ a 0 = c₀ 0 ∧
      b 0 = c₀ 0 + M)
    (hB : ∃ a b, ReachIn ω (latticeBox c₀ M w) a b ∧ a 0 = c₀ 0 ∧ b 0 = c₀ 0 + M)
    (hL : ∃ a b, ReachIn ω (latticeBox c₀ w M) a b ∧ a 1 = c₀ 1 ∧ b 1 = c₀ 1 + M)
    (hR : ∃ a b, ReachIn ω (latticeBox ![c₀ 0 + M - w, c₀ 1] w M) a b ∧ a 1 = c₀ 1 ∧
      b 1 = c₀ 1 + M)
    (hx : ∀ i, c₀ i + w + 3 ≤ x i ∧ x i + w + 4 ≤ c₀ i + M)
    {c : Site 2} {m n : ℕ} (hn : M + 3 ≤ n) :
    (∃ a b, ReachIn ω (latticeBox c m n) a b ∧ a 0 = c 0 ∧ b 0 = c 0 + m) ↔
      (∃ a b, ReachIn ω' (latticeBox c m n) a b ∧ a 0 = c 0 ∧ b 0 = c 0 + m) := by
  have hxS : ∀ (c' : Site 2) (m' n' : ℕ), (x 0 < c' 0 ∨ c' 0 + m' < x 0 ∨ x 1 < c' 1 ∨
      c' 1 + n' < x 1) → x ∉ latticeBox c' m' n' := by
    intro c' m' n' h hmem
    simp only [latticeBox, Set.mem_setOf_eq] at hmem
    omega
  have tr : ∀ (c' : Site 2) (m' n' : ℕ), x ∉ latticeBox c' m' n' → ∀ {a b : Site 2},
      ReachIn ω (latticeBox c' m' n') a b → ReachIn ω' (latticeBox c' m' n') a b :=
    fun c' m' n' hx' a b h => ReachIn.of_adj_iff (adj_iff_of_agree_off_of_notMem hagree hexy hx') h
  have hx0 := hx 0
  have hx1 := hx 1
  have hT' : ∃ a b, ReachIn ω' (latticeBox ![c₀ 0, c₀ 1 + M - w] M w) a b ∧ a 0 = c₀ 0 ∧
      b 0 = c₀ 0 + M := by
    obtain ⟨a, b, h, ha, hb⟩ := hT
    exact ⟨a, b, tr _ _ _ (hxS _ _ _ (Or.inr (Or.inr (Or.inl
      (by change x 1 < c₀ 1 + M - w; omega))))) h, ha, hb⟩
  have hB' : ∃ a b, ReachIn ω' (latticeBox c₀ M w) a b ∧ a 0 = c₀ 0 ∧ b 0 = c₀ 0 + M := by
    obtain ⟨a, b, h, ha, hb⟩ := hB
    exact ⟨a, b, tr _ _ _ (hxS _ _ _ (Or.inr (Or.inr (Or.inr (by omega))))) h, ha, hb⟩
  have hL' : ∃ a b, ReachIn ω' (latticeBox c₀ w M) a b ∧ a 1 = c₀ 1 ∧ b 1 = c₀ 1 + M := by
    obtain ⟨a, b, h, ha, hb⟩ := hL
    exact ⟨a, b, tr _ _ _ (hxS _ _ _ (Or.inr (Or.inl (by omega)))) h, ha, hb⟩
  have hR' : ∃ a b, ReachIn ω' (latticeBox ![c₀ 0 + M - w, c₀ 1] w M) a b ∧ a 1 = c₀ 1 ∧
      b 1 = c₀ 1 + M := by
    obtain ⟨a, b, h, ha, hb⟩ := hR
    exact ⟨a, b, tr _ _ _ (hxS _ _ _ (Or.inl (by change x 0 < c₀ 0 + M - w; omega))) h, ha, hb⟩
  have hagree' : ∀ b, b ≠ e → ω b = ω' b := fun b hb => (hagree b hb).symm
  constructor
  · rintro ⟨a, b, h, ha, hb⟩
    by_contra hno
    exact false_of_flip_crossing hagree' hexy hT' hB' hL' hR' hx hn h ha hb hno
  · rintro ⟨a, b, h, ha, hb⟩
    by_contra hno
    exact false_of_flip_crossing hagree hexy hT hB hL hR hx hn h ha hb hno

/-- **The flip lemma for top-bottom crossings**, by the exchange of the coordinates. -/
theorem vcrossing_iff_of_flip {ω ω' : Configuration 2} {e : Bond 2}
    (hagree : ∀ b, b ≠ e → ω' b = ω b) {x y : Vertex 2} (hexy : e.1 = s(x, y))
    {c₀ : Site 2} {M w : ℕ}
    (hT : ∃ a b, ReachIn ω (latticeBox ![c₀ 0, c₀ 1 + M - w] M w) a b ∧ a 0 = c₀ 0 ∧
      b 0 = c₀ 0 + M)
    (hB : ∃ a b, ReachIn ω (latticeBox c₀ M w) a b ∧ a 0 = c₀ 0 ∧ b 0 = c₀ 0 + M)
    (hL : ∃ a b, ReachIn ω (latticeBox c₀ w M) a b ∧ a 1 = c₀ 1 ∧ b 1 = c₀ 1 + M)
    (hR : ∃ a b, ReachIn ω (latticeBox ![c₀ 0 + M - w, c₀ 1] w M) a b ∧ a 1 = c₀ 1 ∧
      b 1 = c₀ 1 + M)
    (hx : ∀ i, c₀ i + w + 3 ≤ x i ∧ x i + w + 4 ≤ c₀ i + M)
    {c : Site 2} {m n : ℕ} (hm : M + 3 ≤ m) :
    (∃ a b, ReachIn ω (latticeBox c m n) a b ∧ a 1 = c 1 ∧ b 1 = c 1 + n) ↔
      (∃ a b, ReachIn ω' (latticeBox c m n) a b ∧ a 1 = c 1 ∧ b 1 = c 1 + n) := by
  set σω := Rigidity.Proofs.S3.configurationMap swapIso ω
  set σω' := Rigidity.Proofs.S3.configurationMap swapIso ω'
  have hsw : ∀ η : Configuration 2,
      (∃ a b, ReachIn η (latticeBox c m n) a b ∧ a 1 = c 1 ∧ b 1 = c 1 + n) ↔
        (∃ a b, ReachIn (Rigidity.Proofs.S3.configurationMap swapIso η)
          (latticeBox (siteSwap c) n m) a b ∧ a 0 = siteSwap c 0 ∧
            b 0 = siteSwap c 0 + n) := by
    intro η
    constructor
    · rintro ⟨a, b, h, ha, hb⟩
      exact ⟨siteSwap a, siteSwap b, reachIn_swap_box h, by simp [ha], by simp [hb]⟩
    · rintro ⟨a, b, h, ha, hb⟩
      exact ⟨siteSwap a, siteSwap b, reachIn_unswap_box h, by simpa using ha,
        by simpa using hb⟩
  rw [hsw ω, hsw ω']
  have hc₀ : ∀ (u v : ℤ), siteSwap ![u, v] = ![v, u] := fun u v => by
    funext i
    fin_cases i <;> simp
  refine crossing_iff_of_flip (configurationMap_swap_agree_off hagree) (bondMap_swap_val hexy)
    (c₀ := siteSwap c₀) (M := M) (w := w) ?_ ?_ ?_ ?_ (fun i => ?_) hm
  · obtain ⟨a, b, h, ha, hb⟩ := hR
    refine ⟨siteSwap a, siteSwap b, ?_, by simp [ha], by simp [hb]⟩
    have := reachIn_swap_box h
    rw [hc₀] at this
    simpa only [siteSwap_zero, siteSwap_one] using this
  · obtain ⟨a, b, h, ha, hb⟩ := hL
    exact ⟨siteSwap a, siteSwap b, reachIn_swap_box h, by simp [ha], by simp [hb]⟩
  · obtain ⟨a, b, h, ha, hb⟩ := hB
    exact ⟨siteSwap a, siteSwap b, reachIn_swap_box h, by simp [ha], by simp [hb]⟩
  · obtain ⟨a, b, h, ha, hb⟩ := hT
    refine ⟨siteSwap a, siteSwap b, ?_, by simp [ha], by simp [hb]⟩
    have := reachIn_swap_box h
    rw [hc₀] at this
    simpa only [siteSwap_zero, siteSwap_one] using this
  · fin_cases i
    · simpa using hx 1
    · simpa using hx 0

/-! ### Strip meshes -/

theorem IntegerCube.hStrip_eq_latticeBox (R : IntegerCube 2) (r : ℤ) (w : ℕ) :
    R.hStrip r w = latticeBox ![R.corner 0, r] (R.size - 1) w := by
  ext v
  change ((R.corner 0 ≤ v 0 ∧ v 0 ≤ R.corner 0 + ((R.size - 1 : ℕ) : ℤ)) ∧ r ≤ v 1 ∧
    v 1 ≤ r + w) ↔ (R.corner 0 ≤ v 0 ∧ v 0 ≤ R.corner 0 + ((R.size - 1 : ℕ) : ℤ) ∧ r ≤ v 1 ∧
    v 1 ≤ r + w)
  exact and_assoc

theorem IntegerCube.vStrip_eq_latticeBox (R : IntegerCube 2) (r : ℤ) (w : ℕ) :
    R.vStrip r w = latticeBox ![r, R.corner 1] w (R.size - 1) := by
  ext v
  change ((r ≤ v 0 ∧ v 0 ≤ r + w) ∧ R.corner 1 ≤ v 1 ∧ v 1 ≤ R.corner 1 + ((R.size - 1 : ℕ) : ℤ))
    ↔ (r ≤ v 0 ∧ v 0 ≤ r + w ∧ R.corner 1 ≤ v 1 ∧ v 1 ≤ R.corner 1 + ((R.size - 1 : ℕ) : ℤ))
  exact and_assoc

/-- **Strip meshes of width at least `M + 3` do not change when one bond is flipped.** -/
theorem planarMesh_iff_of_flip {ω ω' : Configuration 2} {e : Bond 2}
    (hagree : ∀ b, b ≠ e → ω' b = ω b) {x y : Vertex 2} (hexy : e.1 = s(x, y))
    {c₀ : Site 2} {M w : ℕ}
    (hT : ∃ a b, ReachIn ω (latticeBox ![c₀ 0, c₀ 1 + M - w] M w) a b ∧ a 0 = c₀ 0 ∧
      b 0 = c₀ 0 + M)
    (hB : ∃ a b, ReachIn ω (latticeBox c₀ M w) a b ∧ a 0 = c₀ 0 ∧ b 0 = c₀ 0 + M)
    (hL : ∃ a b, ReachIn ω (latticeBox c₀ w M) a b ∧ a 1 = c₀ 1 ∧ b 1 = c₀ 1 + M)
    (hR : ∃ a b, ReachIn ω (latticeBox ![c₀ 0 + M - w, c₀ 1] w M) a b ∧ a 1 = c₀ 1 ∧
      b 1 = c₀ 1 + M)
    (hx : ∀ i, c₀ i + w + 3 ≤ x i ∧ x i + w + 4 ≤ c₀ i + M)
    (R : IntegerCube 2) {W : ℕ} (hW : M + 3 ≤ W) :
    PlanarMesh ω' R W ↔ PlanarMesh ω R W := by
  unfold PlanarMesh
  simp only [IntegerCube.hStrip_eq_latticeBox, IntegerCube.vStrip_eq_latticeBox]
  refine and_congr (forall_congr' fun r => imp_congr_right fun _ => imp_congr_right fun _ => ?_)
    (forall_congr' fun r => imp_congr_right fun _ => imp_congr_right fun _ => ?_)
  · have h := crossing_iff_of_flip hagree hexy hT hB hL hR hx (c := ![R.corner 0, r])
      (m := R.size - 1) hW
    simp only [Matrix.cons_val_zero] at h
    exact h.symm
  · have h := vcrossing_iff_of_flip hagree hexy hT hB hL hR hx (c := ![r, R.corner 1])
      (n := R.size - 1) hW
    simp only [Matrix.cons_val_one] at h
    exact h.symm

/-! ### Meshed cubes -/

/-- **Flipping one bond changes the meshed cubes only near it**: with `s` the side of the partition
cube of `x`, the meshed cubes of `ω` and `ω'` agree except for cubes of side below `101 s` whose
square of side `9 × side` contains `x`. -/
theorem meshedFlipBound_of_flip {ω ω' : Configuration 2} (hP : PlanarPartitionEvent ω)
    {e : Bond 2} (hagree : ∀ b, b ≠ e → ω' b = ω b) {x y : Vertex 2} (hexy : e.1 = s(x, y)) :
    MeshedFlipBound ω ω' x (101 * (planarPartCube ω x).side) := by
  obtain ⟨hPm, hP8⟩ := planarPartCube_meshed hP x
  have hxP := (planarPartCube_spec hP x).1
  set P := planarPartCube ω x with hPdef
  set k := P.scale with hk
  set s : ℕ := 3 ^ k with hsdef
  have hsZ : (P.side : ℤ) = (s : ℤ) := by
    change (3 : ℤ) ^ P.scale = ((3 ^ k : ℕ) : ℤ)
    push_cast
    rfl
  have hs8 : 6561 ≤ s := by
    have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 3) hP8
    rw [hsdef]
    calc 6561 = 3 ^ 8 := by norm_num
      _ ≤ 3 ^ k := this
  have hsodd : s % 2 = 1 := by
    have : Odd s := by rw [hsdef]; exact Odd.pow (by decide)
    exact Nat.odd_iff.mp this
  set w : ℕ := s / 100 with hw
  set h : ℤ := ((s : ℤ) - 1) / 2 with hh
  set c₀ : Site 2 := fun i => x i - h with hc₀
  set M : ℕ := s - 1 with hM
  set S : IntegerCube 2 := ⟨c₀, s⟩ with hS
  have hSsq : S ∈ P.planarSquares := by
    rw [TriadicCube.mem_planarSquares]
    have hr := P.two_mul_ninefoldRadius
    have h3 : ((3 : ℤ) ^ P.scale) = (s : ℤ) := by rw [← hsZ]; rfl
    rw [h3] at hr
    refine ⟨le_rfl, by change s ≤ 9 * s; omega, fun i => ?_⟩
    have hc := TriadicCube.abs_sub_center_le hxP i
    rw [h3] at hc
    have a1 := le_abs_self (x i - P.center i)
    have a2 := neg_abs_le (x i - P.center i)
    change P.center i - P.ninefoldRadius ≤ x i - h ∧ x i - h + (s : ℤ) ≤
      P.center i + P.ninefoldRadius + 1
    constructor <;> omega
  have hmesh : PlanarMesh ω S w := hPm S hSsq
  have hsS : S.size = s := rfl
  have hc₀2 : (![S.corner 0, S.corner 1] : Site 2) = c₀ := by
    funext i
    fin_cases i <;> rfl
  -- the four outer strips of `S`
  have hB : ∃ a b, ReachIn ω (latticeBox c₀ M w) a b ∧ a 0 = c₀ 0 ∧ b 0 = c₀ 0 + M := by
    obtain ⟨a, b, hab, ha, hb⟩ := hmesh.1 (S.corner 1) le_rfl
      (by change c₀ 1 + w + 1 ≤ c₀ 1 + (s : ℤ); omega)
    rw [IntegerCube.hStrip_eq_latticeBox, hc₀2] at hab
    exact ⟨a, b, hab, ha, hb⟩
  have hT : ∃ a b, ReachIn ω (latticeBox ![c₀ 0, c₀ 1 + M - w] M w) a b ∧ a 0 = c₀ 0 ∧
      b 0 = c₀ 0 + M := by
    obtain ⟨a, b, hab, ha, hb⟩ := hmesh.1 (c₀ 1 + M - w)
      (by change c₀ 1 ≤ c₀ 1 + ((s - 1 : ℕ) : ℤ) - w; omega)
      (by change c₀ 1 + ((s - 1 : ℕ) : ℤ) - w + w + 1 ≤ c₀ 1 + (s : ℤ); omega)
    rw [IntegerCube.hStrip_eq_latticeBox] at hab
    exact ⟨a, b, hab, ha, hb⟩
  have hL : ∃ a b, ReachIn ω (latticeBox c₀ w M) a b ∧ a 1 = c₀ 1 ∧ b 1 = c₀ 1 + M := by
    obtain ⟨a, b, hab, ha, hb⟩ := hmesh.2 (S.corner 0) le_rfl
      (by change c₀ 0 + w + 1 ≤ c₀ 0 + (s : ℤ); omega)
    rw [IntegerCube.vStrip_eq_latticeBox, hc₀2] at hab
    exact ⟨a, b, hab, ha, hb⟩
  have hR : ∃ a b, ReachIn ω (latticeBox ![c₀ 0 + M - w, c₀ 1] w M) a b ∧ a 1 = c₀ 1 ∧
      b 1 = c₀ 1 + M := by
    obtain ⟨a, b, hab, ha, hb⟩ := hmesh.2 (c₀ 0 + M - w)
      (by change c₀ 0 ≤ c₀ 0 + ((s - 1 : ℕ) : ℤ) - w; omega)
      (by change c₀ 0 + ((s - 1 : ℕ) : ℤ) - w + w + 1 ≤ c₀ 0 + (s : ℤ); omega)
    rw [IntegerCube.vStrip_eq_latticeBox] at hab
    exact ⟨a, b, hab, ha, hb⟩
  have hx : ∀ i, c₀ i + w + 3 ≤ x i ∧ x i + w + 4 ≤ c₀ i + M := by
    intro i
    change x i - h + w + 3 ≤ x i ∧ x i + w + 4 ≤ x i - h + ((s - 1 : ℕ) : ℤ)
    omega
  have hexy' : e.1 = s(y, x) := by rw [hexy, Sym2.eq_swap]
  intro A
  by_cases hin : x ∈ (↑A.ninefold.vertices : Set (Vertex 2)) ∧
      y ∈ (↑A.ninefold.vertices : Set (Vertex 2))
  · by_cases hsize : A.side < 101 * P.side
    · right
      refine ⟨hsize, fun i => ?_⟩
      have h1 := TriadicCube.mem_ninefold.1 hin.1 i
      have hr := A.two_mul_ninefoldRadius
      have hA : A.side = 3 ^ A.scale := rfl
      rw [abs_sub_comm]
      rw [hA]
      have hpos : (0 : ℤ) < 3 ^ A.scale := by positivity
      omega
    · left
      push Not at hsize
      have hWA : M + 3 ≤ 3 ^ A.scale / 100 := by
        have h1 : (101 * s : ℤ) ≤ ((3 ^ A.scale : ℕ) : ℤ) := by
          rw [← hsZ]
          push_cast
          exact hsize
        have h2 : 101 * s ≤ 3 ^ A.scale := by exact_mod_cast h1
        omega
      unfold planarMeshedFamily
      simp only [Set.mem_setOf_eq]
      refine and_congr_right fun _ => ?_
      unfold TriadicCube.planarMeshed
      exact forall₂_congr fun R _ => planarMesh_iff_of_flip hagree hexy hT hB hL hR hx R hWA
  · left
    have hloc : ∀ u ∈ (↑A.ninefold.vertices : Set (Vertex 2)),
        ∀ v ∈ (↑A.ninefold.vertices : Set (Vertex 2)),
          ((openGraph ω').Adj u v ↔ (openGraph ω).Adj u v) := by
      rw [not_and_or] at hin
      rcases hin with hxn | hyn
      · exact adj_iff_of_agree_off_of_notMem hagree hexy hxn
      · exact adj_iff_of_agree_off_of_notMem hagree hexy' hyn
    unfold planarMeshedFamily
    simp only [Set.mem_setOf_eq]
    exact and_congr_right fun _ => A.planarMeshed_iff_of_adj_iff hloc

end Rigidity.Percolation
