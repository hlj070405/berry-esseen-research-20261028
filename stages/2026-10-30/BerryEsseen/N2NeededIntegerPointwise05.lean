module

public import BerryEsseen.N2NeededIntegerData
public import BerryEsseen.N2IntegerPointwiseReplay

@[expose] public section

/-! 2026-10-29: integer power numerators and the unchanged original
rows030..034 closed trees. The entries equality is the semantic cache bridge.
No Bernstein coefficient or host closed flag is a premise. -/

namespace BerryEsseen.N2NeededIntegerPointwise05

open N2NeededData N2NeededIntegerData N2IntegerBernstein
  N2IntegerRectangleCertificate N2MajorantPolynomials

def rowIndex (j : Fin 5) : Fin 65 :=
  ⟨5 * 5 + j.val,
    lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (5 * 5)) (by decide)⟩

def signX : Fin 4 → ℚ := N2IntegerPointwiseReplay.signX
def signY : Fin 4 → ℚ := N2IntegerPointwiseReplay.signY

def powers : Fin 5 → Fin 4 → IntPower :=
  ![
    ![
      ![![(330602341908164 : ℤ), (-270157295164125 : ℤ), (-21667887017375 : ℤ), (587143915000 : ℤ)],
        ![(-270157295164125 : ℤ), (49553514696375 : ℤ), (167347420069125 : ℤ), (31780047911625 : ℤ)],
        ![(-21667887017375 : ℤ), (167347420069125 : ℤ), (-153813310465625 : ℤ), (-67723712894375 : ℤ)],
        ![(587143915000 : ℤ), (31780047911625 : ℤ), (-67723712894375 : ℤ), (0 : ℤ)]],
      ![![(330602341908164 : ℤ), (-270157295164125 : ℤ), (-21667887017375 : ℤ), (44161013900500 : ℤ)],
        ![(-270157295164125 : ℤ), (49553514696375 : ℤ), (167347420069125 : ℤ), (-52058267329875 : ℤ)],
        ![(-21667887017375 : ℤ), (167347420069125 : ℤ), (-153813310465625 : ℤ), (22975555078875 : ℤ)],
        ![(587143915000 : ℤ), (31780047911625 : ℤ), (-67723712894375 : ℤ), (0 : ℤ)]],
      ![![(330602341908164 : ℤ), (-270157295164125 : ℤ), (-21667887017375 : ℤ), (587143915000 : ℤ)],
        ![(-270157295164125 : ℤ), (49553514696375 : ℤ), (167347420069125 : ℤ), (31780047911625 : ℤ)],
        ![(-21667887017375 : ℤ), (167347420069125 : ℤ), (-153813310465625 : ℤ), (-67723712894375 : ℤ)],
        ![(44161013900500 : ℤ), (-52058267329875 : ℤ), (22975555078875 : ℤ), (0 : ℤ)]],
      ![![(330602341908164 : ℤ), (-270157295164125 : ℤ), (-21667887017375 : ℤ), (44161013900500 : ℤ)],
        ![(-270157295164125 : ℤ), (49553514696375 : ℤ), (167347420069125 : ℤ), (-52058267329875 : ℤ)],
        ![(-21667887017375 : ℤ), (167347420069125 : ℤ), (-153813310465625 : ℤ), (22975555078875 : ℤ)],
        ![(44161013900500 : ℤ), (-52058267329875 : ℤ), (22975555078875 : ℤ), (0 : ℤ)]]],
    ![
      ![![(333714314359039 : ℤ), (-277595168270375 : ℤ), (-21587646655000 : ℤ), (3055999567750 : ℤ)],
        ![(-277595168270375 : ℤ), (49607736579875 : ℤ), (175883093414750 : ℤ), (29419967148000 : ℤ)],
        ![(-21587646655000 : ℤ), (175883093414750 : ℤ), (-139720723065000 : ℤ), (-67033460759625 : ℤ)],
        ![(3055999567750 : ℤ), (29419967148000 : ℤ), (-67033460759625 : ℤ), (831133813500 : ℤ)]],
      ![![(333714314359039 : ℤ), (-277595168270375 : ℤ), (-21587646655000 : ℤ), (42822059764000 : ℤ)],
        ![(-277595168270375 : ℤ), (49607736579875 : ℤ), (175883093414750 : ℤ), (-60019388387250 : ℤ)],
        ![(-21587646655000 : ℤ), (175883093414750 : ℤ), (-139720723065000 : ℤ), (21033808099125 : ℤ)],
        ![(3055999567750 : ℤ), (29419967148000 : ℤ), (-67033460759625 : ℤ), (11766358463000 : ℤ)]],
      ![![(333714314359039 : ℤ), (-277595168270375 : ℤ), (-21587646655000 : ℤ), (3055999567750 : ℤ)],
        ![(-277595168270375 : ℤ), (49607736579875 : ℤ), (175883093414750 : ℤ), (29419967148000 : ℤ)],
        ![(-21587646655000 : ℤ), (175883093414750 : ℤ), (-139720723065000 : ℤ), (-67033460759625 : ℤ)],
        ![(42822059764000 : ℤ), (-60019388387250 : ℤ), (21033808099125 : ℤ), (11766358463000 : ℤ)]],
      ![![(333714314359039 : ℤ), (-277595168270375 : ℤ), (-21587646655000 : ℤ), (42822059764000 : ℤ)],
        ![(-277595168270375 : ℤ), (49607736579875 : ℤ), (175883093414750 : ℤ), (-60019388387250 : ℤ)],
        ![(-21587646655000 : ℤ), (175883093414750 : ℤ), (-139720723065000 : ℤ), (21033808099125 : ℤ)],
        ![(42822059764000 : ℤ), (-60019388387250 : ℤ), (21033808099125 : ℤ), (1030420859500 : ℤ)]]],
    ![
      ![![(338467684157664 : ℤ), (-284481772733250 : ℤ), (-17725382898500 : ℤ), (3358641672625 : ℤ)],
        ![(-284481772733250 : ℤ), (37538544001000 : ℤ), (182945901942125 : ℤ), (37881838758625 : ℤ)],
        ![(-17725382898500 : ℤ), (182945901942125 : ℤ), (-157189163900000 : ℤ), (-70053556546250 : ℤ)],
        ![(3358641672625 : ℤ), (37881838758625 : ℤ), (-70053556546250 : ℤ), (0 : ℤ)]],
      ![![(338467684157664 : ℤ), (-284481772733250 : ℤ), (-17725382898500 : ℤ), (44139236363625 : ℤ)],
        ![(-284481772733250 : ℤ), (37538544001000 : ℤ), (182945901942125 : ℤ), (-54836244190875 : ℤ)],
        ![(-17725382898500 : ℤ), (182945901942125 : ℤ), (-157189163900000 : ℤ), (22555678510000 : ℤ)],
        ![(3358641672625 : ℤ), (37881838758625 : ℤ), (-70053556546250 : ℤ), (0 : ℤ)]],
      ![![(338467684157664 : ℤ), (-284481772733250 : ℤ), (-17725382898500 : ℤ), (3358641672625 : ℤ)],
        ![(-284481772733250 : ℤ), (37538544001000 : ℤ), (182945901942125 : ℤ), (37881838758625 : ℤ)],
        ![(-17725382898500 : ℤ), (182945901942125 : ℤ), (-157189163900000 : ℤ), (-70053556546250 : ℤ)],
        ![(44139236363625 : ℤ), (-54836244190875 : ℤ), (22555678510000 : ℤ), (0 : ℤ)]],
      ![![(338467684157664 : ℤ), (-284481772733250 : ℤ), (-17725382898500 : ℤ), (44139236363625 : ℤ)],
        ![(-284481772733250 : ℤ), (37538544001000 : ℤ), (182945901942125 : ℤ), (-54836244190875 : ℤ)],
        ![(-17725382898500 : ℤ), (182945901942125 : ℤ), (-157189163900000 : ℤ), (22555678510000 : ℤ)],
        ![(44139236363625 : ℤ), (-54836244190875 : ℤ), (22555678510000 : ℤ), (0 : ℤ)]]],
    ![
      ![![(346172873645664 : ℤ), (-289419045352750 : ℤ), (-21669688852125 : ℤ), (3052218764500 : ℤ)],
        ![(-289419045352750 : ℤ), (33260120436375 : ℤ), (185652804248500 : ℤ), (36923182909500 : ℤ)],
        ![(-21669688852125 : ℤ), (185652804248500 : ℤ), (-150602582797875 : ℤ), (-69768294186000 : ℤ)],
        ![(3052218764500 : ℤ), (36923182909500 : ℤ), (-69768294186000 : ℤ), (0 : ℤ)]],
      ![![(346172873645664 : ℤ), (-289419045352750 : ℤ), (-21669688852125 : ℤ), (46014573237250 : ℤ)],
        ![(-289419045352750 : ℤ), (33260120436375 : ℤ), (185652804248500 : ℤ), (-54186652457500 : ℤ)],
        ![(-21669688852125 : ℤ), (185652804248500 : ℤ), (-150602582797875 : ℤ), (20701502184250 : ℤ)],
        ![(3052218764500 : ℤ), (36923182909500 : ℤ), (-69768294186000 : ℤ), (0 : ℤ)]],
      ![![(346172873645664 : ℤ), (-289419045352750 : ℤ), (-21669688852125 : ℤ), (3052218764500 : ℤ)],
        ![(-289419045352750 : ℤ), (33260120436375 : ℤ), (185652804248500 : ℤ), (36923182909500 : ℤ)],
        ![(-21669688852125 : ℤ), (185652804248500 : ℤ), (-150602582797875 : ℤ), (-69768294186000 : ℤ)],
        ![(46014573237250 : ℤ), (-54186652457500 : ℤ), (20701502184250 : ℤ), (0 : ℤ)]],
      ![![(346172873645664 : ℤ), (-289419045352750 : ℤ), (-21669688852125 : ℤ), (46014573237250 : ℤ)],
        ![(-289419045352750 : ℤ), (33260120436375 : ℤ), (185652804248500 : ℤ), (-54186652457500 : ℤ)],
        ![(-21669688852125 : ℤ), (185652804248500 : ℤ), (-150602582797875 : ℤ), (20701502184250 : ℤ)],
        ![(46014573237250 : ℤ), (-54186652457500 : ℤ), (20701502184250 : ℤ), (0 : ℤ)]]],
    ![
      ![![(354023188029414 : ℤ), (-297064003168000 : ℤ), (-26843713377500 : ℤ), (1899579928000 : ℤ)],
        ![(-297064003168000 : ℤ), (21890217306625 : ℤ), (197040389684625 : ℤ), (43017954312375 : ℤ)],
        ![(-26843713377500 : ℤ), (197040389684625 : ℤ), (-136522700416125 : ℤ), (-65579648007625 : ℤ)],
        ![(1899579928000 : ℤ), (43017954312375 : ℤ), (-65579648007625 : ℤ), (1943171148250 : ℤ)]],
      ![![(354023188029414 : ℤ), (-297064003168000 : ℤ), (-26843713377500 : ℤ), (49486852998000 : ℤ)],
        ![(-297064003168000 : ℤ), (21890217306625 : ℤ), (197040389684625 : ℤ), (-55717371764125 : ℤ)],
        ![(-26843713377500 : ℤ), (197040389684625 : ℤ), (-136522700416125 : ℤ), (12795586741375 : ℤ)],
        ![(1899579928000 : ℤ), (43017954312375 : ℤ), (-65579648007625 : ℤ), (-2641985318250 : ℤ)]],
      ![![(354023188029414 : ℤ), (-297064003168000 : ℤ), (-26843713377500 : ℤ), (1899579928000 : ℤ)],
        ![(-297064003168000 : ℤ), (21890217306625 : ℤ), (197040389684625 : ℤ), (43017954312375 : ℤ)],
        ![(-26843713377500 : ℤ), (197040389684625 : ℤ), (-136522700416125 : ℤ), (-65579648007625 : ℤ)],
        ![(49486852998000 : ℤ), (-55717371764125 : ℤ), (12795586741375 : ℤ), (-2641985318250 : ℤ)]],
      ![![(354023188029414 : ℤ), (-297064003168000 : ℤ), (-26843713377500 : ℤ), (49486852998000 : ℤ)],
        ![(-297064003168000 : ℤ), (21890217306625 : ℤ), (197040389684625 : ℤ), (-55717371764125 : ℤ)],
        ![(-26843713377500 : ℤ), (197040389684625 : ℤ), (-136522700416125 : ℤ), (12795586741375 : ℤ)],
        ![(49486852998000 : ℤ), (-55717371764125 : ℤ), (12795586741375 : ℤ), (3340799488250 : ℤ)]]]]

theorem powers_entries :
    ∀ (j : Fin 5) (o r s : Fin 4), (powers j o r s : ℚ) / (D : ℚ) =
      orthantPower (coefficients (rowIndex j)) (signX o) (signY o) (1 / 1000) r s := by
  decide +kernel

theorem powers_eq (j : Fin 5) (o : Fin 4) :
    rationalPower (powers j o) D =
      orthantPower (coefficients (rowIndex j))
        (N2IntegerPointwiseReplay.signX o) (N2IntegerPointwiseReplay.signY o) (1 / 1000) := by
  funext r s
  exact powers_entries j o r s

def trees : Fin 5 → Fin 4 → Certificate :=
  ![
    ![
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          Certificate.inside
          (Certificate.splitX (-1152 : ℤ)
            Certificate.inside
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              Certificate.inside)))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            Certificate.inside
            Certificate.inside)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              (Certificate.splitX (-576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-480 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  Certificate.inside)))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    Certificate.inside))
                Certificate.inside)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (-336 : ℤ)
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-360 : ℤ)
                            Certificate.inside
                            Certificate.inside))
                        (Certificate.splitY (-336 : ℤ)
                          (Certificate.splitX (-312 : ℤ)
                            Certificate.inside
                            Certificate.inside)
                          Certificate.inside))
                      Certificate.inside)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                        (Certificate.cross (-463542214290501 : ℤ) (1759218604441600 : ℕ) none)))))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-48 : ℤ)
                        (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                        (Certificate.cross (-463542214290501 : ℤ) (1759218604441600 : ℕ) none))))
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                          (Certificate.splitX (-120 : ℤ)
                            (Certificate.splitY (-120 : ℤ)
                              (Certificate.cross (-6716480880672510951 : ℤ) (115292150460684697600 : ℕ) none)
                              (Certificate.cross (-33955792251685852947 : ℤ) (122497909864477491200 : ℕ) none))
                            (Certificate.cross (-559568073331845399 : ℤ) (1801439850948198400 : ℕ) none))))
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (-48 : ℤ)
                          (Certificate.cross (-8451569425503249759 : ℤ) (28823037615171174400 : ℕ) none)
                          Certificate.outside)
                        Certificate.outside))
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (-48 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.cross (-8451569425503249759 : ℤ) (28823037615171174400 : ℕ) none)
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)))))))),
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-1344 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                Certificate.inside)
              Certificate.inside)
            (Certificate.cross (0 : ℤ) (1 : ℕ) none))
          (Certificate.cross (0 : ℤ) (1 : ℕ) none))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-480 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-432 : ℤ)
                        (Certificate.cross (-85897928330005971 : ℤ) (450359962737049600 : ℕ) none)
                        (Certificate.splitY (144 : ℤ)
                          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                          (Certificate.splitX (-408 : ℤ)
                            (Certificate.cross (-18376988764638355143 : ℤ) (30624477466119372800 : ℕ) none)
                            (Certificate.cross (-12908219063979667 : ℤ) (21110623253299200 : ℕ) none))))))
                  (Certificate.splitX (-480 : ℤ)
                    (Certificate.cross (-86131025498514003 : ℤ) (365917469723852800 : ℕ) none)
                    (Certificate.cross (-2289750345863697 : ℤ) (3518437208883200 : ℕ) none))))
              (Certificate.cross (-536732785358547 : ℤ) (1044536046387200 : ℕ) none))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.cross (-162327957744636381 : ℤ) (450359962737049600 : ℕ) none)
                      (Certificate.cross (-17194999126089891 : ℤ) (28147497671065600 : ℕ) none))
                    (Certificate.cross (-1480675855206309387 : ℤ) (2589569785738035200 : ℕ) none))
                  Certificate.outside)
                Certificate.outside)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      Certificate.outside))
                  Certificate.outside)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (432 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (-168 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (456 : ℤ)
                              Certificate.outside
                              Certificate.outside)))
                        (Certificate.splitY (432 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (-120 : ℤ)
                            (Certificate.splitY (456 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            Certificate.outside)))
                      (Certificate.splitX (-144 : ℤ)
                        Certificate.outside
                        Certificate.outside))
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      Certificate.outside))
                  Certificate.outside))))
          (Certificate.splitX (-384 : ℤ)
            Certificate.outside
            Certificate.outside))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                Certificate.inside)
              Certificate.inside)
            (Certificate.cross (0 : ℤ) (1 : ℕ) none))
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (96 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-480 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (144 : ℤ)
                        (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                        (Certificate.splitY (-432 : ℤ)
                          (Certificate.cross (-85897928330005971 : ℤ) (450359962737049600 : ℕ) none)
                          (Certificate.splitX (168 : ℤ)
                            (Certificate.cross (-4311750048115821567 : ℤ) (7656119366529843200 : ℕ) none)
                            (Certificate.cross (-47393975071457439 : ℤ) (77405618595430400 : ℕ) none)))))))
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-480 : ℤ)
                      (Certificate.cross (-16205406819868887 : ℤ) (900719925474099200 : ℕ) none)
                      (Certificate.cross (-54224079150065813 : ℤ) (84442493013196800 : ℕ) none))
                    (Certificate.cross (-400282167664420503 : ℤ) (647392446434508800 : ℕ) none))))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.cross (-1128218103530131137 : ℤ) (2589569785738035200 : ℕ) none)
                    (Certificate.cross (-17194999126089891 : ℤ) (28147497671065600 : ℕ) none))
                  Certificate.outside)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  Certificate.outside)))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (-536732785358547 : ℤ) (1044536046387200 : ℕ) none)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    Certificate.outside
                    Certificate.outside)
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (432 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (456 : ℤ)
                            Certificate.outside
                            Certificate.outside)
                          (Certificate.splitX (456 : ℤ)
                            Certificate.outside
                            Certificate.outside)))
                      Certificate.outside)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (528 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)))
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  Certificate.outside)))))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              Certificate.outside
              Certificate.outside)
            Certificate.outside))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      Certificate.outside))))
              Certificate.outside)
            (Certificate.splitY (384 : ℤ)
              Certificate.outside
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (528 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (528 : ℤ)
                          Certificate.outside
                          Certificate.outside))))
                  (Certificate.splitX (480 : ℤ)
                    Certificate.outside
                    Certificate.outside))
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (672 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    Certificate.outside)
                  Certificate.outside))))
          (Certificate.splitX (384 : ℤ)
            Certificate.outside
            Certificate.outside))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              Certificate.outside
              Certificate.outside)
            (Certificate.splitY (384 : ℤ)
              Certificate.outside
              Certificate.outside))
          Certificate.outside))],
    ![
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          Certificate.inside
          (Certificate.splitX (-1152 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              Certificate.inside)
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              (Certificate.splitX (-960 : ℤ)
                Certificate.inside
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  Certificate.inside)))))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            Certificate.inside
            (Certificate.splitY (-1152 : ℤ)
              Certificate.inside
              (Certificate.splitX (-192 : ℤ)
                Certificate.inside
                Certificate.inside)))
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              (Certificate.splitX (-576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-480 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  Certificate.inside)))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    Certificate.inside))
                Certificate.inside)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (-336 : ℤ)
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-360 : ℤ)
                            Certificate.inside
                            Certificate.inside))
                        (Certificate.splitY (-336 : ℤ)
                          (Certificate.splitX (-312 : ℤ)
                            Certificate.inside
                            Certificate.inside)
                          Certificate.inside))
                      Certificate.inside)
                    Certificate.inside)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.inside
                      (Certificate.cross (-680877580392377 : ℤ) (2638827906662400 : ℕ) none))))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.cross (-680877580392377 : ℤ) (2638827906662400 : ℕ) none)))
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-120 : ℤ)
                            (Certificate.cross (-34155216102360199519 : ℤ) (129703669268270284800 : ℕ) none)
                            (Certificate.splitY (-120 : ℤ)
                              (Certificate.cross (-34155216102360199519 : ℤ) (129703669268270284800 : ℕ) none)
                              (Certificate.cross (-1731197120073146221 : ℤ) (5404319552844595200 : ℕ) none)))))
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (-48 : ℤ)
                          (Certificate.cross (-103105502217718140019 : ℤ) (345876451382054092800 : ℕ) none)
                          (Certificate.cross (-137766064062725003 : ℤ) (379991218559385600 : ℕ) none))
                        (Certificate.cross (-29475898999202641 : ℤ) (73887181386547200 : ℕ) none)))
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (-48 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.cross (-103105502217718140019 : ℤ) (345876451382054092800 : ℕ) none)
                          (Certificate.cross (-35378391457275309143 : ℤ) (97277751951202713600 : ℕ) none))
                        (Certificate.cross (-29475898999202641 : ℤ) (73887181386547200 : ℕ) none))
                      Certificate.outside)))))))),
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-1344 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-1440 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.splitX (-1488 : ℤ)
                        (Certificate.splitY (48 : ℤ)
                          (Certificate.splitX (-1512 : ℤ)
                            (Certificate.splitY (24 : ℤ)
                              (Certificate.splitX (-1524 : ℤ)
                                (Certificate.splitY (12 : ℤ)
                                  (Certificate.splitX (-1530 : ℤ)
                                    (Certificate.splitY (6 : ℤ)
                                      Certificate.inside
                                      Certificate.inside)
                                    Certificate.inside)
                                  Certificate.inside)
                                Certificate.inside)
                              Certificate.inside)
                            Certificate.inside)
                          Certificate.inside)
                        Certificate.inside)
                      Certificate.inside)
                    Certificate.inside)
                  Certificate.inside)
                Certificate.inside)
              Certificate.inside)
            (Certificate.cross (0 : ℤ) (1 : ℕ) none))
          (Certificate.cross (-548106543434461 : ℤ) (494780232499200 : ℕ) none))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-480 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-432 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (144 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-7632625680908141 : ℤ) (12314530231091200 : ℕ) none)))))
                  (Certificate.splitX (-480 : ℤ)
                    (Certificate.cross (-70991236776403439 : ℤ) (154811237190860800 : ℕ) none)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.cross (-152037126129464439 : ℤ) (225179981368524800 : ℕ) none)
                      Certificate.outside))))
              (Certificate.cross (-4932556929330751 : ℤ) (7916483719987200 : ℕ) none))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.cross (-938680884489865673 : ℤ) (2702159776422297600 : ℕ) none)
                      (Certificate.splitX (-336 : ℤ)
                        (Certificate.splitY (144 : ℤ)
                          (Certificate.cross (-84454431141826449947 : ℤ) (172938225691027046400 : ℕ) none)
                          (Certificate.cross (-13073210721271891 : ℤ) (21110623253299200 : ℕ) none))
                        (Certificate.cross (-7355830031531082721 : ℤ) (12159718993900339200 : ℕ) none)))
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.cross (-1069456054670316137 : ℤ) (2364389804369510400 : ℕ) none)
                      Certificate.outside))
                  Certificate.outside)
                Certificate.outside)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      Certificate.outside))
                  Certificate.outside)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (432 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (432 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (-120 : ℤ)
                            (Certificate.splitY (456 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (456 : ℤ)
                              Certificate.outside
                              Certificate.outside))))
                      Certificate.outside)
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (-48 : ℤ)
                        (Certificate.splitY (432 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside))
                  Certificate.outside))))
          Certificate.outside)),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-1344 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (-1440 : ℤ)
                      (Certificate.splitX (48 : ℤ)
                        (Certificate.splitY (-1488 : ℤ)
                          (Certificate.splitX (24 : ℤ)
                            (Certificate.splitY (-1512 : ℤ)
                              (Certificate.splitX (12 : ℤ)
                                (Certificate.splitY (-1524 : ℤ)
                                  (Certificate.splitX (6 : ℤ)
                                    Certificate.inside
                                    Certificate.inside)
                                  Certificate.inside)
                                Certificate.inside)
                              Certificate.inside)
                            Certificate.inside)
                          Certificate.inside)
                        Certificate.inside)
                      Certificate.inside)
                    Certificate.inside)
                  Certificate.inside)
                Certificate.inside)
              Certificate.inside)
            (Certificate.cross (0 : ℤ) (1 : ℕ) none))
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (96 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-480 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (144 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-432 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-7632625680908141 : ℤ) (12314530231091200 : ℕ) none))))))
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-480 : ℤ)
                      (Certificate.cross (-725747264477914673 : ℤ) (2702159776422297600 : ℕ) none)
                      (Certificate.cross (-152037126129464439 : ℤ) (225179981368524800 : ℕ) none))
                    (Certificate.cross (-396927952816812503 : ℤ) (591097451092377600 : ℕ) none))))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.cross (-938680884489865673 : ℤ) (2702159776422297600 : ℕ) none)
                      (Certificate.cross (-1069456054670316137 : ℤ) (2364389804369510400 : ℕ) none))
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (144 : ℤ)
                        (Certificate.cross (-6232676707469871721 : ℤ) (12159718993900339200 : ℕ) none)
                        (Certificate.cross (-13073210721271891 : ℤ) (21110623253299200 : ℕ) none))
                      Certificate.outside))
                  Certificate.outside)
                Certificate.outside))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (-4932556929330751 : ℤ) (7916483719987200 : ℕ) none)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    Certificate.outside
                    Certificate.outside)
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (432 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (456 : ℤ)
                            Certificate.outside
                            Certificate.outside)))
                      (Certificate.splitX (432 : ℤ)
                        Certificate.outside
                        Certificate.outside))
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)))
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  Certificate.outside)))))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.cross (-548106543434461 : ℤ) (494780232499200 : ℕ) none)
          Certificate.outside)),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      Certificate.outside))))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    Certificate.outside)
                  Certificate.outside)
                Certificate.outside))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    Certificate.outside
                    Certificate.outside)
                  Certificate.outside)
                Certificate.outside)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (528 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (528 : ℤ)
                          Certificate.outside
                          Certificate.outside))))
                  (Certificate.splitX (480 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (672 : ℤ)
                      (Certificate.splitX (528 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      Certificate.outside)))
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (672 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (624 : ℤ)
                        (Certificate.splitY (528 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside))
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      Certificate.outside))
                  Certificate.outside))))
          (Certificate.splitX (384 : ℤ)
            Certificate.outside
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (576 : ℤ)
                Certificate.outside
                Certificate.outside)
              Certificate.outside)))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              Certificate.outside
              (Certificate.splitX (960 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                (Certificate.splitY (576 : ℤ)
                  Certificate.outside
                  Certificate.outside)))
            (Certificate.splitY (384 : ℤ)
              Certificate.outside
              Certificate.outside))
          Certificate.outside))],
    ![
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          Certificate.inside
          (Certificate.splitX (-1152 : ℤ)
            Certificate.inside
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              Certificate.inside)))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            Certificate.inside
            Certificate.inside)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              (Certificate.splitX (-576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-480 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  Certificate.inside)))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    Certificate.inside))
                Certificate.inside)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (-336 : ℤ)
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-360 : ℤ)
                            Certificate.inside
                            Certificate.inside))
                        (Certificate.splitY (-336 : ℤ)
                          (Certificate.splitX (-312 : ℤ)
                            (Certificate.splitY (-360 : ℤ)
                              Certificate.inside
                              Certificate.inside)
                            Certificate.inside)
                          Certificate.inside))
                      Certificate.inside)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.inside
                      (Certificate.cross (-596112321052379 : ℤ) (3518437208883200 : ℕ) none))))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    Certificate.inside
                    (Certificate.cross (-596112321052379 : ℤ) (3518437208883200 : ℕ) none))
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-120 : ℤ)
                            (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                            (Certificate.splitY (-120 : ℤ)
                              (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                              (Certificate.cross (-146257773943596637 : ℤ) (450359962737049600 : ℕ) none)))))
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (-48 : ℤ)
                          (Certificate.cross (-1972622236134302317 : ℤ) (7205759403792793600 : ℕ) none)
                          (Certificate.cross (-235410721013847881 : ℤ) (647392446434508800 : ℕ) none))
                        (Certificate.splitY (-48 : ℤ)
                          (Certificate.splitX (-120 : ℤ)
                            (Certificate.cross (-154124475650246528519 : ℤ) (446757083035153203200 : ℕ) none)
                            Certificate.outside)
                          Certificate.outside)))
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (-48 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.cross (-1972622236134302317 : ℤ) (7205759403792793600 : ℕ) none)
                          (Certificate.splitX (-72 : ℤ)
                            (Certificate.cross (-39642506573918627411 : ℤ) (111689270758788300800 : ℕ) none)
                            Certificate.outside))
                        (Certificate.cross (-54925932951000907 : ℤ) (133700613937561600 : ℕ) none))
                      Certificate.outside)))))))),
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-1344 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-1440 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.splitX (-1488 : ℤ)
                        (Certificate.splitY (48 : ℤ)
                          (Certificate.splitX (-1512 : ℤ)
                            (Certificate.splitY (24 : ℤ)
                              Certificate.inside
                              (Certificate.splitX (-1524 : ℤ)
                                (Certificate.splitY (36 : ℤ)
                                  (Certificate.splitX (-1530 : ℤ)
                                    (Certificate.splitY (30 : ℤ)
                                      Certificate.inside
                                      Certificate.inside)
                                    Certificate.inside)
                                  Certificate.inside)
                                Certificate.inside))
                            Certificate.inside)
                          Certificate.inside)
                        (Certificate.splitY (48 : ℤ)
                          Certificate.inside
                          Certificate.inside))
                      Certificate.inside)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  Certificate.inside)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  Certificate.inside))
              Certificate.inside)
            (Certificate.cross (0 : ℤ) (1 : ℕ) none))
          (Certificate.cross (0 : ℤ) (1 : ℕ) none))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-480 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-432 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (144 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-4363670982313633 : ℤ) (7036874417766400 : ℕ) none)))))
                  (Certificate.splitX (-480 : ℤ)
                    (Certificate.cross (-19817427199489003 : ℤ) (253327479039590400 : ℕ) none)
                    (Certificate.cross (-1777615978532563 : ℤ) (2638827906662400 : ℕ) none))))
              (Certificate.cross (-3913066491652751 : ℤ) (7476679068876800 : ℕ) none))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.cross (-207692240663511899 : ℤ) (900719925474099200 : ℕ) none)
                      (Certificate.splitX (-336 : ℤ)
                        (Certificate.splitY (144 : ℤ)
                          (Certificate.cross (-12707617398908963143 : ℤ) (28823037615171174400 : ℕ) none)
                          (Certificate.cross (-57298759226260439 : ℤ) (91479367430963200 : ℕ) none))
                        (Certificate.cross (-3181801042324580173 : ℤ) (5179139571476070400 : ℕ) none)))
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.cross (-121708107472833689 : ℤ) (267401227875123200 : ℕ) none)
                      Certificate.outside))
                  Certificate.outside)
                Certificate.outside)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      Certificate.outside))
                  Certificate.outside)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (432 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (432 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (-120 : ℤ)
                            (Certificate.splitY (456 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            Certificate.outside)))
                      (Certificate.splitX (-144 : ℤ)
                        Certificate.outside
                        Certificate.outside))
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      Certificate.outside))
                  Certificate.outside))))
          (Certificate.splitX (-384 : ℤ)
            Certificate.outside
            Certificate.outside))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-1344 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (-1440 : ℤ)
                      (Certificate.splitX (48 : ℤ)
                        (Certificate.splitY (-1488 : ℤ)
                          (Certificate.splitX (24 : ℤ)
                            Certificate.inside
                            (Certificate.splitY (-1512 : ℤ)
                              (Certificate.splitX (36 : ℤ)
                                (Certificate.splitY (-1524 : ℤ)
                                  (Certificate.splitX (30 : ℤ)
                                    Certificate.inside
                                    Certificate.inside)
                                  Certificate.inside)
                                Certificate.inside)
                              Certificate.inside))
                          Certificate.inside)
                        Certificate.inside)
                      Certificate.inside)
                    Certificate.inside)
                  Certificate.inside)
                Certificate.inside)
              Certificate.inside)
            (Certificate.cross (0 : ℤ) (1 : ℕ) none))
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (96 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-480 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (144 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-432 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-4363670982313633 : ℤ) (7036874417766400 : ℕ) none))))))
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-480 : ℤ)
                      (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                      (Certificate.cross (-65351484329896657 : ℤ) (98516241848729600 : ℕ) none))
                    (Certificate.cross (-169812706421691689 : ℤ) (267401227875123200 : ℕ) none))))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.cross (-121708107472833689 : ℤ) (267401227875123200 : ℕ) none)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (144 : ℤ)
                        (Certificate.cross (-5277992892547135721 : ℤ) (10358279142952140800 : ℕ) none)
                        (Certificate.cross (-39844075297005907 : ℤ) (63331869759897600 : ℕ) none))
                      Certificate.outside))
                  Certificate.outside)
                Certificate.outside))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (-3913066491652751 : ℤ) (7476679068876800 : ℕ) none)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    Certificate.outside
                    Certificate.outside)
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (432 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (456 : ℤ)
                            Certificate.outside
                            Certificate.outside)))
                      Certificate.outside)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (528 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)))
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  Certificate.outside)))))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              Certificate.outside
              Certificate.outside)
            Certificate.outside))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      Certificate.outside))))
              Certificate.outside)
            (Certificate.splitY (384 : ℤ)
              Certificate.outside
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (480 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (672 : ℤ)
                      Certificate.outside
                      Certificate.outside)))
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (672 : ℤ)
                    Certificate.outside
                    Certificate.outside)
                  (Certificate.splitX (672 : ℤ)
                    (Certificate.splitY (672 : ℤ)
                      (Certificate.splitX (624 : ℤ)
                        (Certificate.splitY (624 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)
                    Certificate.outside)))))
          (Certificate.splitX (384 : ℤ)
            Certificate.outside
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (576 : ℤ)
                Certificate.outside
                Certificate.outside)
              Certificate.outside)))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              Certificate.outside
              (Certificate.splitX (960 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                Certificate.outside))
            (Certificate.splitY (384 : ℤ)
              Certificate.outside
              Certificate.outside))
          Certificate.outside))],
    ![
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          Certificate.inside
          (Certificate.splitX (-1152 : ℤ)
            Certificate.inside
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              Certificate.inside)))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            Certificate.inside
            Certificate.inside)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              (Certificate.splitX (-576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-480 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  Certificate.inside)))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    Certificate.inside))
                Certificate.inside)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (-336 : ℤ)
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.inside
                          Certificate.inside))
                      Certificate.inside)
                    Certificate.inside)
                  (Certificate.cross (0 : ℤ) (1 : ℕ) none))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-120 : ℤ)
                            Certificate.inside
                            (Certificate.cross (-34085467740361631 : ℤ) (112589990684262400 : ℕ) none))))
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (-48 : ℤ)
                          (Certificate.cross (-367126242183086471 : ℤ) (1801439850948198400 : ℕ) none)
                          (Certificate.cross (-49340806742886689 : ℤ) (133700613937561600 : ℕ) none))
                        (Certificate.splitY (-48 : ℤ)
                          (Certificate.splitX (-120 : ℤ)
                            (Certificate.cross (-621778755607831691 : ℤ) (1801439850948198400 : ℕ) none)
                            (Certificate.cross (-204280709166657881 : ℤ) (534802455750246400 : ℕ) none))
                          Certificate.outside)))
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (-48 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.cross (-367126242183086471 : ℤ) (1801439850948198400 : ℕ) none)
                          (Certificate.splitX (-72 : ℤ)
                            (Certificate.cross (-3708562340220823567 : ℤ) (10358279142952140800 : ℕ) none)
                            (Certificate.cross (-204280709166657881 : ℤ) (534802455750246400 : ℕ) none)))
                        (Certificate.cross (-12577159050085633 : ℤ) (29906716275507200 : ℕ) none))
                      Certificate.outside)))))))),
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-1344 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-1440 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.splitX (-1488 : ℤ)
                        (Certificate.splitY (48 : ℤ)
                          (Certificate.splitX (-1512 : ℤ)
                            (Certificate.splitY (24 : ℤ)
                              Certificate.inside
                              (Certificate.splitX (-1524 : ℤ)
                                (Certificate.splitY (36 : ℤ)
                                  (Certificate.splitX (-1530 : ℤ)
                                    (Certificate.splitY (30 : ℤ)
                                      Certificate.inside
                                      Certificate.inside)
                                    Certificate.inside)
                                  Certificate.inside)
                                Certificate.inside))
                            Certificate.inside)
                          Certificate.inside)
                        (Certificate.splitY (48 : ℤ)
                          Certificate.inside
                          Certificate.inside))
                      Certificate.inside)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  Certificate.inside)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  Certificate.inside))
              Certificate.inside)
            (Certificate.cross (0 : ℤ) (1 : ℕ) none))
          (Certificate.cross (0 : ℤ) (1 : ℕ) none))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-480 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-432 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (144 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-2150884843664383 : ℤ) (3518437208883200 : ℕ) none)))))
                  (Certificate.cross (-6341267421028877 : ℤ) (9675702324428800 : ℕ) none)))
              (Certificate.cross (-875832437416469 : ℤ) (1759218604441600 : ℕ) none))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.cross (-35286405708642149 : ℤ) (450359962737049600 : ℕ) none)
                      (Certificate.splitX (-336 : ℤ)
                        (Certificate.splitY (144 : ℤ)
                          (Certificate.cross (-5926179015563640643 : ℤ) (14411518807585587200 : ℕ) none)
                          (Certificate.cross (-2253896807752073 : ℤ) (3518437208883200 : ℕ) none))
                        (Certificate.cross (-675835337589473887 : ℤ) (1069604911500492800 : ℕ) none)))
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.cross (-449659800629234381 : ℤ) (957014920816230400 : ℕ) none)
                      Certificate.outside))
                  Certificate.outside)
                Certificate.outside)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      Certificate.outside))
                  Certificate.outside)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (432 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (-120 : ℤ)
                            (Certificate.splitY (456 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (456 : ℤ)
                              Certificate.outside
                              Certificate.outside))))
                      (Certificate.splitX (-144 : ℤ)
                        Certificate.outside
                        Certificate.outside))
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (-48 : ℤ)
                        (Certificate.splitY (432 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside))
                  Certificate.outside))))
          (Certificate.splitX (-384 : ℤ)
            Certificate.outside
            Certificate.outside))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-1344 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (-1440 : ℤ)
                      (Certificate.splitX (48 : ℤ)
                        (Certificate.splitY (-1488 : ℤ)
                          (Certificate.splitX (24 : ℤ)
                            Certificate.inside
                            (Certificate.splitY (-1512 : ℤ)
                              (Certificate.splitX (36 : ℤ)
                                (Certificate.splitY (-1524 : ℤ)
                                  (Certificate.splitX (30 : ℤ)
                                    Certificate.inside
                                    Certificate.inside)
                                  Certificate.inside)
                                Certificate.inside)
                              Certificate.inside))
                          Certificate.inside)
                        Certificate.inside)
                      Certificate.inside)
                    Certificate.inside)
                  Certificate.inside)
                Certificate.inside)
              Certificate.inside)
            (Certificate.cross (0 : ℤ) (1 : ℕ) none))
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (96 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-480 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (144 : ℤ)
                        Certificate.inside
                        (Certificate.cross (-2150884843664383 : ℤ) (3518437208883200 : ℕ) none)))))
                (Certificate.cross (-6341267421028877 : ℤ) (9675702324428800 : ℕ) none))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.cross (-35286405708642149 : ℤ) (450359962737049600 : ℕ) none)
                      (Certificate.cross (-449659800629234381 : ℤ) (957014920816230400 : ℕ) none))
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (144 : ℤ)
                        (Certificate.cross (-9060114356016606067 : ℤ) (17113678584007884800 : ℕ) none)
                        (Certificate.splitY (-336 : ℤ)
                          (Certificate.cross (-2253896807752073 : ℤ) (3518437208883200 : ℕ) none)
                          Certificate.outside))
                      Certificate.outside))
                  Certificate.outside)
                Certificate.outside))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (-875832437416469 : ℤ) (1759218604441600 : ℕ) none)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    Certificate.outside
                    Certificate.outside)
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (432 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (456 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (-120 : ℤ)
                              Certificate.outside
                              Certificate.outside))))
                      (Certificate.splitX (432 : ℤ)
                        Certificate.outside
                        Certificate.outside))
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (528 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)))
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  Certificate.outside)))))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              Certificate.outside
              Certificate.outside)
            Certificate.outside))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (96 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      Certificate.outside)))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    Certificate.outside
                    Certificate.outside)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      Certificate.outside))))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                Certificate.outside))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (576 : ℤ)
                Certificate.outside
                Certificate.outside)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                (Certificate.splitY (576 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (672 : ℤ)
                    (Certificate.splitY (672 : ℤ)
                      (Certificate.splitX (624 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (624 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (648 : ℤ)
                            Certificate.outside
                            Certificate.outside)))
                      (Certificate.splitX (624 : ℤ)
                        Certificate.outside
                        Certificate.outside))
                    (Certificate.splitY (672 : ℤ)
                      (Certificate.splitX (720 : ℤ)
                        (Certificate.splitY (624 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside))))))
          (Certificate.splitX (384 : ℤ)
            Certificate.outside
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (576 : ℤ)
                Certificate.outside
                Certificate.outside)
              Certificate.outside)))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              Certificate.outside
              (Certificate.splitX (960 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                Certificate.outside))
            (Certificate.splitY (384 : ℤ)
              Certificate.outside
              Certificate.outside))
          Certificate.outside))],
    ![
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          Certificate.inside
          (Certificate.splitX (-1152 : ℤ)
            Certificate.inside
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              Certificate.inside)))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            Certificate.inside
            Certificate.inside)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              (Certificate.splitX (-576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-480 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  Certificate.inside)))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    Certificate.inside))
                Certificate.inside)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (-336 : ℤ)
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-360 : ℤ)
                            Certificate.inside
                            Certificate.inside))
                        (Certificate.splitY (-336 : ℤ)
                          (Certificate.splitX (-312 : ℤ)
                            (Certificate.splitY (-360 : ℤ)
                              Certificate.inside
                              Certificate.inside)
                            Certificate.inside)
                          Certificate.inside))
                      Certificate.inside)
                    Certificate.inside)
                  Certificate.inside)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (-48 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-1198903269706627 : ℤ) (3298534883328000 : ℕ) none))
                        (Certificate.splitY (-48 : ℤ)
                          (Certificate.splitX (-120 : ℤ)
                            (Certificate.cross (-1143045154657749388679 : ℤ) (3458764513820540928000 : ℕ) none)
                            (Certificate.splitY (-72 : ℤ)
                              (Certificate.cross (-152630677371575837413 : ℤ) (432345564227567616000 : ℕ) none)
                              (Certificate.cross (-41607077156645025911 : ℤ) (108086391056891904000 : ℕ) none)))
                          (Certificate.cross (-1411339120393001 : ℤ) (3298534883328000 : ℕ) none))))
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (-48 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-72 : ℤ)
                            (Certificate.cross (-152630677371575837413 : ℤ) (432345564227567616000 : ℕ) none)
                            (Certificate.cross (-41607077156645025911 : ℤ) (108086391056891904000 : ℕ) none)))
                        (Certificate.cross (-1411339120393001 : ℤ) (3298534883328000 : ℕ) none))
                      (Certificate.cross (-97866312929293 : ℤ) (206158430208000 : ℕ) none))))))))),
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-1344 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-1440 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.splitX (-1488 : ℤ)
                        (Certificate.splitY (48 : ℤ)
                          (Certificate.splitX (-1512 : ℤ)
                            (Certificate.splitY (24 : ℤ)
                              Certificate.inside
                              (Certificate.splitX (-1524 : ℤ)
                                (Certificate.splitY (36 : ℤ)
                                  Certificate.inside
                                  (Certificate.splitX (-1530 : ℤ)
                                    (Certificate.splitY (42 : ℤ)
                                      Certificate.inside
                                      Certificate.inside)
                                    Certificate.inside))
                                Certificate.inside))
                            Certificate.inside)
                          Certificate.inside)
                        (Certificate.splitY (48 : ℤ)
                          Certificate.inside
                          Certificate.inside))
                      Certificate.inside)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  Certificate.inside)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  Certificate.inside))
              Certificate.inside)
            (Certificate.cross (0 : ℤ) (1 : ℕ) none))
          (Certificate.cross (0 : ℤ) (1 : ℕ) none))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                Certificate.inside
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.cross (-5786427975491627 : ℤ) (8796093022208000 : ℕ) none)))
              (Certificate.cross (-6616795056071377 : ℤ) (13194139533312000 : ℕ) none))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-336 : ℤ)
                        (Certificate.splitY (144 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-356762619494037137 : ℤ) (562949953421312000 : ℕ) none))
                        (Certificate.cross (-8519751238195035067 : ℤ) (13510798882111488000 : ℕ) none)))
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.cross (-1603125291903240149 : ℤ) (3377699720527872000 : ℕ) none)
                      (Certificate.cross (-2082469857231654899 : ℤ) (3377699720527872000 : ℕ) none)))
                  (Certificate.cross (-12998023275252461 : ℤ) (17592186044416000 : ℕ) none))
                (Certificate.cross (-96625651694546391 : ℤ) (140737488355328000 : ℕ) none))
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      Certificate.outside))
                  Certificate.outside)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (432 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (-120 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (456 : ℤ)
                              Certificate.outside
                              Certificate.outside))))
                      (Certificate.splitX (-144 : ℤ)
                        Certificate.outside
                        Certificate.outside))
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (-48 : ℤ)
                        (Certificate.splitY (432 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside))
                  Certificate.outside))))
          (Certificate.splitX (-384 : ℤ)
            Certificate.outside
            Certificate.outside))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-1344 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (-1440 : ℤ)
                      (Certificate.splitX (48 : ℤ)
                        (Certificate.splitY (-1488 : ℤ)
                          (Certificate.splitX (24 : ℤ)
                            Certificate.inside
                            (Certificate.splitY (-1512 : ℤ)
                              (Certificate.splitX (36 : ℤ)
                                Certificate.inside
                                (Certificate.splitY (-1524 : ℤ)
                                  (Certificate.splitX (42 : ℤ)
                                    Certificate.inside
                                    Certificate.inside)
                                  Certificate.inside))
                              Certificate.inside))
                          Certificate.inside)
                        Certificate.inside)
                      Certificate.inside)
                    Certificate.inside)
                  Certificate.inside)
                Certificate.inside)
              Certificate.inside)
            (Certificate.cross (0 : ℤ) (1 : ℕ) none))
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                (Certificate.cross (-5786427975491627 : ℤ) (8796093022208000 : ℕ) none))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.cross (-1603125291903240149 : ℤ) (3377699720527872000 : ℕ) none))
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (144 : ℤ)
                        (Certificate.cross (-56188223209338141911 : ℤ) (108086391056891904000 : ℕ) none)
                        (Certificate.splitY (-336 : ℤ)
                          (Certificate.cross (-356762619494037137 : ℤ) (562949953421312000 : ℕ) none)
                          (Certificate.cross (-8519751238195035067 : ℤ) (13510798882111488000 : ℕ) none)))
                      (Certificate.cross (-2082469857231654899 : ℤ) (3377699720527872000 : ℕ) none)))
                  (Certificate.cross (-487994579409295003 : ℤ) (844424930131968000 : ℕ) none))
                (Certificate.cross (-27421213874774129 : ℤ) (35184372088832000 : ℕ) none)))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (-6616795056071377 : ℤ) (13194139533312000 : ℕ) none)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    Certificate.outside
                    Certificate.outside)
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (432 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (456 : ℤ)
                            Certificate.outside
                            Certificate.outside)))
                      (Certificate.splitX (432 : ℤ)
                        Certificate.outside
                        Certificate.outside))
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (528 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)))
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  Certificate.outside)))))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              Certificate.outside
              Certificate.outside)
            Certificate.outside))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (96 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      Certificate.outside)))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    Certificate.outside
                    Certificate.outside)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      Certificate.outside)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      Certificate.outside))))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                Certificate.outside))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (576 : ℤ)
                Certificate.outside
                Certificate.outside)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                (Certificate.splitY (576 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (672 : ℤ)
                    (Certificate.splitY (672 : ℤ)
                      (Certificate.splitX (624 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (624 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (648 : ℤ)
                            Certificate.outside
                            Certificate.outside)))
                      (Certificate.splitX (624 : ℤ)
                        Certificate.outside
                        Certificate.outside))
                    (Certificate.splitY (672 : ℤ)
                      (Certificate.splitX (720 : ℤ)
                        (Certificate.splitY (624 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside))))))
          (Certificate.splitX (384 : ℤ)
            Certificate.outside
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (576 : ℤ)
                Certificate.outside
                Certificate.outside)
              Certificate.outside)))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              Certificate.outside
              (Certificate.splitX (960 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                (Certificate.splitY (576 : ℤ)
                  Certificate.outside
                  Certificate.outside)))
            (Certificate.splitY (384 : ℤ)
              Certificate.outside
              Certificate.outside))
          Certificate.outside))]]

def integerChecks (j : Fin 5) : Bool :=
  N2IntegerPointwiseReplay.fourChecks (powers j) D S (tNum (rowIndex j)) (trees j)

theorem checks : ∀ j : Fin 5, integerChecks j = true := by
  decide +kernel

theorem pointwise (j : Fin 5) (x y : ℝ) (hx : |x| ≤ 6) (hy : |y| ≤ 6) :
    N2MomentMajorant.closedIndicator (upperQ (rowIndex j) : ℝ) x y ≤
      N2MomentMajorant.majorant (coefficients (rowIndex j)) x y + (1 : ℝ) / 1000 := by
  have hp := N2IntegerPointwiseReplay.pointwise_of_fourChecks
    (coefficients (rowIndex j)) (1 / 1000) (powers j) D S (tNum (rowIndex j))
    (trees j) D_pos S_pos (powers_eq j) (checks j) x y hx hy
  rw [← upperQ_eq_tNum] at hp
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hp

end BerryEsseen.N2NeededIntegerPointwise05

#print axioms BerryEsseen.N2NeededIntegerPointwise05.powers_entries
#print axioms BerryEsseen.N2NeededIntegerPointwise05.powers_eq
#print axioms BerryEsseen.N2NeededIntegerPointwise05.checks
#print axioms BerryEsseen.N2NeededIntegerPointwise05.pointwise
