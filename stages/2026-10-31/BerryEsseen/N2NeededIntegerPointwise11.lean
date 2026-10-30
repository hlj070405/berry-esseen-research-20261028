module

public import BerryEsseen.N2NeededIntegerData
public import BerryEsseen.N2IntegerPointwiseReplay

@[expose] public section

/-! 2026-10-29: integer power numerators and the unchanged original
rows060..064 closed trees. The entries equality is the semantic cache bridge.
No Bernstein coefficient or host closed flag is a premise. -/

namespace BerryEsseen.N2NeededIntegerPointwise11

open N2NeededData N2NeededIntegerData N2IntegerBernstein
  N2IntegerRectangleCertificate N2MajorantPolynomials

def rowIndex (j : Fin 5) : Fin 65 :=
  ⟨11 * 5 + j.val,
    lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (11 * 5)) (by decide)⟩

def signX : Fin 4 → ℚ := N2IntegerPointwiseReplay.signX
def signY : Fin 4 → ℚ := N2IntegerPointwiseReplay.signY

def powers : Fin 5 → Fin 4 → IntPower :=
  ![
    ![
      ![![(605660207324664 : ℤ), (-35215914881000 : ℤ), (-129013843321250 : ℤ), (-61880182687750 : ℤ)],
        ![(-35215914881000 : ℤ), (-178345549208000 : ℤ), (-95163737922875 : ℤ), (12418884221750 : ℤ)],
        ![(-129013843321250 : ℤ), (-95163737922875 : ℤ), (1621624643375 : ℤ), (4373738081000 : ℤ)],
        ![(-61880182687750 : ℤ), (12418884221750 : ℤ), (4373738081000 : ℤ), (-404693546875 : ℤ)]],
      ![![(605660207324664 : ℤ), (-35215914881000 : ℤ), (-129013843321250 : ℤ), (32112186511500 : ℤ)],
        ![(-35215914881000 : ℤ), (-178345549208000 : ℤ), (-95163737922875 : ℤ), (54896648865750 : ℤ)],
        ![(-129013843321250 : ℤ), (-95163737922875 : ℤ), (1621624643375 : ℤ), (27578921456500 : ℤ)],
        ![(-61880182687750 : ℤ), (12418884221750 : ℤ), (4373738081000 : ℤ), (1182477922875 : ℤ)]],
      ![![(605660207324664 : ℤ), (-35215914881000 : ℤ), (-129013843321250 : ℤ), (-61880182687750 : ℤ)],
        ![(-35215914881000 : ℤ), (-178345549208000 : ℤ), (-95163737922875 : ℤ), (12418884221750 : ℤ)],
        ![(-129013843321250 : ℤ), (-95163737922875 : ℤ), (1621624643375 : ℤ), (4373738081000 : ℤ)],
        ![(32112186511500 : ℤ), (54896648865750 : ℤ), (27578921456500 : ℤ), (1182477922875 : ℤ)]],
      ![![(605660207324664 : ℤ), (-35215914881000 : ℤ), (-129013843321250 : ℤ), (32112186511500 : ℤ)],
        ![(-35215914881000 : ℤ), (-178345549208000 : ℤ), (-95163737922875 : ℤ), (54896648865750 : ℤ)],
        ![(-129013843321250 : ℤ), (-95163737922875 : ℤ), (1621624643375 : ℤ), (27578921456500 : ℤ)],
        ![(32112186511500 : ℤ), (54896648865750 : ℤ), (27578921456500 : ℤ), (-3431401168875 : ℤ)]]],
    ![
      ![![(605194765475039 : ℤ), (-22273754526500 : ℤ), (-126707950638375 : ℤ), (-64584661268125 : ℤ)],
        ![(-22273754526500 : ℤ), (-159393459897125 : ℤ), (-114070555872125 : ℤ), (-1946587188875 : ℤ)],
        ![(-126707950638375 : ℤ), (-114070555872125 : ℤ), (2562484920125 : ℤ), (12243759588625 : ℤ)],
        ![(-64584661268125 : ℤ), (-1946587188875 : ℤ), (12243759588625 : ℤ), (2790515521875 : ℤ)]],
      ![![(605194765475039 : ℤ), (-22273754526500 : ℤ), (-126707950638375 : ℤ), (31612504980625 : ℤ)],
        ![(-22273754526500 : ℤ), (-159393459897125 : ℤ), (-114070555872125 : ℤ), (58813673744375 : ℤ)],
        ![(-126707950638375 : ℤ), (-114070555872125 : ℤ), (2562484920125 : ℤ), (29479621499875 : ℤ)],
        ![(-64584661268125 : ℤ), (-1946587188875 : ℤ), (12243759588625 : ℤ), (509282948625 : ℤ)]],
      ![![(605194765475039 : ℤ), (-22273754526500 : ℤ), (-126707950638375 : ℤ), (-64584661268125 : ℤ)],
        ![(-22273754526500 : ℤ), (-159393459897125 : ℤ), (-114070555872125 : ℤ), (-1946587188875 : ℤ)],
        ![(-126707950638375 : ℤ), (-114070555872125 : ℤ), (2562484920125 : ℤ), (12243759588625 : ℤ)],
        ![(31612504980625 : ℤ), (58813673744375 : ℤ), (29479621499875 : ℤ), (509282948625 : ℤ)]],
      ![![(605194765475039 : ℤ), (-22273754526500 : ℤ), (-126707950638375 : ℤ), (31612504980625 : ℤ)],
        ![(-22273754526500 : ℤ), (-159393459897125 : ℤ), (-114070555872125 : ℤ), (58813673744375 : ℤ)],
        ![(-126707950638375 : ℤ), (-114070555872125 : ℤ), (2562484920125 : ℤ), (29479621499875 : ℤ)],
        ![(31612504980625 : ℤ), (58813673744375 : ℤ), (29479621499875 : ℤ), (-7833090464125 : ℤ)]]],
    ![
      ![![(604877232409289 : ℤ), (-13641409570000 : ℤ), (-119758161849125 : ℤ), (-62928702189125 : ℤ)],
        ![(-13641409570000 : ℤ), (-139613548411375 : ℤ), (-115009264733375 : ℤ), (-8848590074125 : ℤ)],
        ![(-119758161849125 : ℤ), (-115009264733375 : ℤ), (7885420679625 : ℤ), (18365707466375 : ℤ)],
        ![(-62928702189125 : ℤ), (-8848590074125 : ℤ), (18365707466375 : ℤ), (5687017863125 : ℤ)]],
      ![![(604877232409289 : ℤ), (-13641409570000 : ℤ), (-119758161849125 : ℤ), (28256094844375 : ℤ)],
        ![(-13641409570000 : ℤ), (-139613548411375 : ℤ), (-115009264733375 : ℤ), (51318150895375 : ℤ)],
        ![(-119758161849125 : ℤ), (-115009264733375 : ℤ), (7885420679625 : ℤ), (20029722922375 : ℤ)],
        ![(-62928702189125 : ℤ), (-8848590074125 : ℤ), (18365707466375 : ℤ), (-3825606341125 : ℤ)]],
      ![![(604877232409289 : ℤ), (-13641409570000 : ℤ), (-119758161849125 : ℤ), (-62928702189125 : ℤ)],
        ![(-13641409570000 : ℤ), (-139613548411375 : ℤ), (-115009264733375 : ℤ), (-8848590074125 : ℤ)],
        ![(-119758161849125 : ℤ), (-115009264733375 : ℤ), (7885420679625 : ℤ), (18365707466375 : ℤ)],
        ![(28256094844375 : ℤ), (51318150895375 : ℤ), (20029722922375 : ℤ), (-3825606341125 : ℤ)]],
      ![![(604877232409289 : ℤ), (-13641409570000 : ℤ), (-119758161849125 : ℤ), (28256094844375 : ℤ)],
        ![(-13641409570000 : ℤ), (-139613548411375 : ℤ), (-115009264733375 : ℤ), (51318150895375 : ℤ)],
        ![(-119758161849125 : ℤ), (-115009264733375 : ℤ), (7885420679625 : ℤ), (20029722922375 : ℤ)],
        ![(28256094844375 : ℤ), (51318150895375 : ℤ), (20029722922375 : ℤ), (1964194819125 : ℤ)]]],
    ![
      ![![(606618418015164 : ℤ), (-8250944147875 : ℤ), (-114436749124250 : ℤ), (-59971855494375 : ℤ)],
        ![(-8250944147875 : ℤ), (-125294320935375 : ℤ), (-117471145468750 : ℤ), (-17280967149125 : ℤ)],
        ![(-114436749124250 : ℤ), (-117471145468750 : ℤ), (5659913874625 : ℤ), (21104899683000 : ℤ)],
        ![(-59971855494375 : ℤ), (-17280967149125 : ℤ), (21104899683000 : ℤ), (8470529903625 : ℤ)]],
      ![![(606618418015164 : ℤ), (-8250944147875 : ℤ), (-114436749124250 : ℤ), (26383933161125 : ℤ)],
        ![(-8250944147875 : ℤ), (-125294320935375 : ℤ), (-117471145468750 : ℤ), (49276993922625 : ℤ)],
        ![(-114436749124250 : ℤ), (-117471145468750 : ℤ), (5659913874625 : ℤ), (18027982184250 : ℤ)],
        ![(-59971855494375 : ℤ), (-17280967149125 : ℤ), (21104899683000 : ℤ), (-5698050136625 : ℤ)]],
      ![![(606618418015164 : ℤ), (-8250944147875 : ℤ), (-114436749124250 : ℤ), (-59971855494375 : ℤ)],
        ![(-8250944147875 : ℤ), (-125294320935375 : ℤ), (-117471145468750 : ℤ), (-17280967149125 : ℤ)],
        ![(-114436749124250 : ℤ), (-117471145468750 : ℤ), (5659913874625 : ℤ), (21104899683000 : ℤ)],
        ![(26383933161125 : ℤ), (49276993922625 : ℤ), (18027982184250 : ℤ), (-5698050136625 : ℤ)]],
      ![![(606618418015164 : ℤ), (-8250944147875 : ℤ), (-114436749124250 : ℤ), (26383933161125 : ℤ)],
        ![(-8250944147875 : ℤ), (-125294320935375 : ℤ), (-117471145468750 : ℤ), (49276993922625 : ℤ)],
        ![(-114436749124250 : ℤ), (-117471145468750 : ℤ), (5659913874625 : ℤ), (18027982184250 : ℤ)],
        ![(26383933161125 : ℤ), (49276993922625 : ℤ), (18027982184250 : ℤ), (2925570369625 : ℤ)]]],
    ![
      ![![(611946152133289 : ℤ), (-6186377864000 : ℤ), (-113273605381625 : ℤ), (-57307905635500 : ℤ)],
        ![(-6186377864000 : ℤ), (-119478879304875 : ℤ), (-115067133512750 : ℤ), (-19632652167250 : ℤ)],
        ![(-113273605381625 : ℤ), (-115067133512750 : ℤ), (6886345376750 : ℤ), (21971735312125 : ℤ)],
        ![(-57307905635500 : ℤ), (-19632652167250 : ℤ), (21971735312125 : ℤ), (9614927840625 : ℤ)]],
      ![![(611946152133289 : ℤ), (-6186377864000 : ℤ), (-113273605381625 : ℤ), (25101613653750 : ℤ)],
        ![(-6186377864000 : ℤ), (-119478879304875 : ℤ), (-115067133512750 : ℤ), (46578500998500 : ℤ)],
        ![(-113273605381625 : ℤ), (-115067133512750 : ℤ), (6886345376750 : ℤ), (16162948108125 : ℤ)],
        ![(-57307905635500 : ℤ), (-19632652167250 : ℤ), (21971735312125 : ℤ), (-6650732121375 : ℤ)]],
      ![![(611946152133289 : ℤ), (-6186377864000 : ℤ), (-113273605381625 : ℤ), (-57307905635500 : ℤ)],
        ![(-6186377864000 : ℤ), (-119478879304875 : ℤ), (-115067133512750 : ℤ), (-19632652167250 : ℤ)],
        ![(-113273605381625 : ℤ), (-115067133512750 : ℤ), (6886345376750 : ℤ), (21971735312125 : ℤ)],
        ![(25101613653750 : ℤ), (46578500998500 : ℤ), (16162948108125 : ℤ), (-6650732121375 : ℤ)]],
      ![![(611946152133289 : ℤ), (-6186377864000 : ℤ), (-113273605381625 : ℤ), (25101613653750 : ℤ)],
        ![(-6186377864000 : ℤ), (-119478879304875 : ℤ), (-115067133512750 : ℤ), (46578500998500 : ℤ)],
        ![(-113273605381625 : ℤ), (-115067133512750 : ℤ), (6886345376750 : ℤ), (16162948108125 : ℤ)],
        ![(25101613653750 : ℤ), (46578500998500 : ℤ), (16162948108125 : ℤ), (3686536402125 : ℤ)]]]]

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
        Certificate.inside
        (Certificate.splitY (-768 : ℤ)
          Certificate.inside
          (Certificate.splitX (-384 : ℤ)
            Certificate.inside
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.inside
                        Certificate.inside)
                      Certificate.inside)))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-144 : ℤ)
                        Certificate.inside
                        Certificate.inside))
                    Certificate.inside)
                  Certificate.inside)))))),
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              Certificate.inside
              (Certificate.splitX (-1344 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                Certificate.inside))
            (Certificate.splitY (384 : ℤ)
              Certificate.inside
              (Certificate.splitX (-960 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                Certificate.inside)))
          (Certificate.cross (0 : ℤ) (1 : ℕ) none))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-672 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-624 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (336 : ℤ)
                          Certificate.inside
                          Certificate.inside)))))
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-480 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-528 : ℤ)
                        Certificate.inside
                        Certificate.inside)
                      (Certificate.splitX (-528 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          (Certificate.splitX (-552 : ℤ)
                            (Certificate.splitY (312 : ℤ)
                              Certificate.inside
                              Certificate.inside)
                            Certificate.inside)
                          Certificate.inside)
                        Certificate.inside))
                    (Certificate.splitY (288 : ℤ)
                      Certificate.inside
                      Certificate.inside))))
              (Certificate.splitX (-576 : ℤ)
                (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                (Certificate.cross (0 : ℤ) (1 : ℕ) none)))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                        (Certificate.splitY (336 : ℤ)
                          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                          (Certificate.splitX (-216 : ℤ)
                            (Certificate.cross (-1570261929808600259 : ℤ) (15312238733059686400 : ℕ) none)
                            (Certificate.cross (-8285961484791907 : ℤ) (56294995342131200 : ℕ) none)))))))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-48 : ℤ)
                        (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                        (Certificate.splitY (144 : ℤ)
                          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                          (Certificate.splitX (-24 : ℤ)
                            (Certificate.cross (-26113635875587850947 : ℤ) (122497909864477491200 : ℕ) none)
                            (Certificate.cross (-472488014524001 : ℤ) (1759218604441600 : ℕ) none))))))
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                          (Certificate.splitX (-120 : ℤ)
                            (Certificate.cross (-159402603415963770701 : ℤ) (979983278915819929600 : ℕ) none)
                            (Certificate.cross (-5823788710511513009 : ℤ) (28823037615171174400 : ℕ) none))))
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          (Certificate.splitX (-168 : ℤ)
                            (Certificate.cross (-1127919500600892898483 : ℤ) (7839866231326559436800 : ℕ) none)
                            (Certificate.cross (-327423584361602858951 : ℤ) (1844674407370955161600 : ℕ) none))
                          Certificate.outside)
                        Certificate.outside))
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-48 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.splitX (-72 : ℤ)
                            (Certificate.cross (-1429760739819044526733 : ℤ) (7839866231326559436800 : ℕ) none)
                            (Certificate.cross (-426337533821093360951 : ℤ) (1844674407370955161600 : ℕ) none))
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside))))
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.cross (-321090455215286923 : ℤ) (10358279142952140800 : ℕ) none)
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.cross (-49947494817522545947 : ℤ) (446757083035153203200 : ℕ) none)
                        Certificate.outside)
                      Certificate.outside))
                  Certificate.outside)
                Certificate.outside)))
          (Certificate.splitX (-384 : ℤ)
            (Certificate.cross (0 : ℤ) (1 : ℕ) none)
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                Certificate.outside
                Certificate.outside)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (1344 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (1440 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (1488 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (-216 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (1512 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (-204 : ℤ)
                                Certificate.outside
                                Certificate.outside))))))))
                (Certificate.splitY (1344 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    Certificate.outside
                    Certificate.outside)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (1440 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    Certificate.outside))))))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            Certificate.inside
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (576 : ℤ)
                Certificate.inside
                Certificate.inside)
              (Certificate.splitX (576 : ℤ)
                Certificate.inside
                Certificate.inside)))
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-672 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (336 : ℤ)
                        Certificate.inside
                        Certificate.inside)))
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-480 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-528 : ℤ)
                          Certificate.inside
                          Certificate.inside))
                      Certificate.inside)
                    (Certificate.splitY (-480 : ℤ)
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.splitY (-528 : ℤ)
                          (Certificate.splitX (312 : ℤ)
                            Certificate.inside
                            Certificate.inside)
                          Certificate.inside)
                        Certificate.inside)
                      Certificate.inside))))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (96 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (144 : ℤ)
                        (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                        (Certificate.splitY (-48 : ℤ)
                          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                          (Certificate.splitX (168 : ℤ)
                            (Certificate.cross (-112165066783724137 : ℤ) (478507460408115200 : ℕ) none)
                            (Certificate.cross (-472488014524001 : ℤ) (1759218604441600 : ℕ) none)))))))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                          (Certificate.splitX (360 : ℤ)
                            (Certificate.cross (-15708526030581959197 : ℤ) (122497909864477491200 : ℕ) none)
                            (Certificate.cross (-8285961484791907 : ℤ) (56294995342131200 : ℕ) none))))))
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                          (Certificate.splitX (264 : ℤ)
                            (Certificate.cross (-168116771537379662201 : ℤ) (979983278915819929600 : ℕ) none)
                            (Certificate.cross (-5823788710511513009 : ℤ) (28823037615171174400 : ℕ) none))))
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (-48 : ℤ)
                          (Certificate.splitX (216 : ℤ)
                            (Certificate.cross (-1536904954835634433483 : ℤ) (7839866231326559436800 : ℕ) none)
                            (Certificate.cross (-426337533821093360951 : ℤ) (1844674407370955161600 : ℕ) none))
                          Certificate.outside)
                        Certificate.outside))
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (312 : ℤ)
                            (Certificate.cross (-1208954157744793893733 : ℤ) (7839866231326559436800 : ℕ) none)
                            (Certificate.cross (-327423584361602858951 : ℤ) (1844674407370955161600 : ℕ) none))
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)))))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.cross (0 : ℤ) (1 : ℕ) none))
                (Certificate.cross (0 : ℤ) (1 : ℕ) none))
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                      (Certificate.splitX (432 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.cross (-166279139190738401951 : ℤ) (1844674407370955161600 : ℕ) none)
                          Certificate.outside)
                        Certificate.outside))
                    (Certificate.cross (-423392423267160881 : ℤ) (2139209823000985600 : ℕ) none))
                  Certificate.outside)
                Certificate.outside))))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)
              (Certificate.splitX (960 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  Certificate.outside)))
            (Certificate.splitY (-384 : ℤ)
              Certificate.outside
              (Certificate.splitX (1344 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (1248 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (1440 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1488 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1512 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (1524 : ℤ)
                                Certificate.outside
                                (Certificate.splitY (-204 : ℤ)
                                  Certificate.outside
                                  Certificate.outside))))))))
                  (Certificate.splitX (1440 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)))))))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.splitX (48 : ℤ)
                        (Certificate.cross (-460075918890764947 : ℤ) (14411518807585587200 : ℕ) none)
                        (Certificate.splitY (48 : ℤ)
                          (Certificate.cross (-460075918890764947 : ℤ) (14411518807585587200 : ℕ) none)
                          (Certificate.splitX (72 : ℤ)
                            (Certificate.splitY (72 : ℤ)
                              (Certificate.cross (-467422404078754759739 : ℤ) (7378697629483820646400 : ℕ) none)
                              (Certificate.cross (-286135398538968299201 : ℤ) (979983278915819929600 : ℕ) none))
                            (Certificate.splitY (72 : ℤ)
                              (Certificate.cross (-286135398538968299201 : ℤ) (979983278915819929600 : ℕ) none)
                              Certificate.outside))))
                      (Certificate.splitX (48 : ℤ)
                        (Certificate.splitY (144 : ℤ)
                          (Certificate.splitX (24 : ℤ)
                            (Certificate.cross (-2029575631140964883233 : ℤ) (7839866231326559436800 : ℕ) none)
                            (Certificate.cross (-570339724370824079201 : ℤ) (1844674407370955161600 : ℕ) none))
                          Certificate.outside)
                        Certificate.outside))
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.splitX (144 : ℤ)
                        (Certificate.splitY (48 : ℤ)
                          (Certificate.splitX (120 : ℤ)
                            (Certificate.splitY (24 : ℤ)
                              (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                              (Certificate.cross (-2195039612094258914983 : ℤ) (7839866231326559436800 : ℕ) none))
                            (Certificate.cross (-570339724370824079201 : ℤ) (1844674407370955161600 : ℕ) none))
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside))
                  Certificate.outside)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (360 : ℤ)
                            (Certificate.splitY (360 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            Certificate.outside)))))))
              (Certificate.splitX (192 : ℤ)
                Certificate.outside
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (336 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      Certificate.outside))
                  Certificate.outside)))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (432 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside))
                    Certificate.outside))
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  Certificate.outside))
              Certificate.outside))
          Certificate.outside)
        Certificate.outside)],
    ![
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (-1152 : ℤ)
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (-1344 : ℤ)
                (Certificate.splitY (-1344 : ℤ)
                  (Certificate.splitX (-1440 : ℤ)
                    (Certificate.splitY (-1440 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-1488 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-1392 : ℤ)
                          (Certificate.splitX (-1464 : ℤ)
                            Certificate.inside
                            (Certificate.splitY (-1416 : ℤ)
                              Certificate.inside
                              Certificate.inside))
                          Certificate.inside)))
                    (Certificate.splitY (-1440 : ℤ)
                      (Certificate.splitX (-1392 : ℤ)
                        (Certificate.splitY (-1488 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-1416 : ℤ)
                            (Certificate.splitY (-1464 : ℤ)
                              Certificate.inside
                              Certificate.inside)
                            Certificate.inside))
                        Certificate.inside)
                      (Certificate.splitX (-1392 : ℤ)
                        (Certificate.splitY (-1392 : ℤ)
                          (Certificate.splitX (-1416 : ℤ)
                            (Certificate.splitY (-1416 : ℤ)
                              Certificate.inside
                              Certificate.inside)
                            Certificate.inside)
                          Certificate.inside)
                        Certificate.inside)))
                  Certificate.inside)
                (Certificate.splitY (-1344 : ℤ)
                  Certificate.inside
                  Certificate.inside))
              Certificate.inside)
            Certificate.inside)
          Certificate.inside)
        (Certificate.splitY (-768 : ℤ)
          Certificate.inside
          (Certificate.splitX (-384 : ℤ)
            Certificate.inside
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.inside
                        Certificate.inside)
                      Certificate.inside)))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-144 : ℤ)
                        Certificate.inside
                        Certificate.inside))
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  Certificate.inside)))))),
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              Certificate.inside
              (Certificate.splitX (-1344 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-1440 : ℤ)
                    (Certificate.splitY (672 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-1488 : ℤ)
                        (Certificate.splitY (720 : ℤ)
                          (Certificate.splitX (-1512 : ℤ)
                            (Certificate.splitY (696 : ℤ)
                              (Certificate.splitX (-1524 : ℤ)
                                (Certificate.splitY (684 : ℤ)
                                  Certificate.inside
                                  Certificate.inside)
                                Certificate.inside)
                              Certificate.inside)
                            Certificate.inside)
                          Certificate.inside)
                        Certificate.inside))
                    Certificate.inside))
                (Certificate.splitY (576 : ℤ)
                  Certificate.inside
                  Certificate.inside)))
            (Certificate.splitY (384 : ℤ)
              Certificate.inside
              Certificate.inside))
          (Certificate.cross (0 : ℤ) (1 : ℕ) none))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-480 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-432 : ℤ)
                        Certificate.inside
                        Certificate.inside)
                      Certificate.inside))))
              (Certificate.cross (0 : ℤ) (1 : ℕ) none))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (336 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-216 : ℤ)
                            (Certificate.cross (-77404120867588753 : ℤ) (2702159776422297600 : ℕ) none)
                            (Certificate.cross (-1520299331316469 : ℤ) (14073748835532800 : ℕ) none)))))))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-48 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (144 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-24 : ℤ)
                            (Certificate.cross (-2735568645520913399 : ℤ) (21617278211378380800 : ℕ) none)
                            (Certificate.cross (-409665301402043 : ℤ) (1759218604441600 : ℕ) none))))))
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-120 : ℤ)
                            (Certificate.cross (-16514199394577531317 : ℤ) (172938225691027046400 : ℕ) none)
                            (Certificate.cross (-1177904911959176753 : ℤ) (7205759403792793600 : ℕ) none))))
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          (Certificate.splitX (-168 : ℤ)
                            (Certificate.cross (-122976095939056661411 : ℤ) (1383505805528216371200 : ℕ) none)
                            (Certificate.cross (-65094683120229314567 : ℤ) (461168601842738790400 : ℕ) none))
                          (Certificate.cross (-335967148327271891 : ℤ) (2026619832316723200 : ℕ) none))
                        (Certificate.cross (-84120186639331377 : ℤ) (394064967394918400 : ℕ) none)))
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-48 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.cross (-88190578023174944567 : ℤ) (461168601842738790400 : ℕ) none)
                          (Certificate.cross (-29954143074067060649 : ℤ) (129703669268270284800 : ℕ) none))
                        (Certificate.cross (-14502058425830469 : ℤ) (49258120924364800 : ℕ) none))
                      Certificate.outside))))
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.cross (-8718983106196590899 : ℤ) (129703669268270284800 : ℕ) none)
                        (Certificate.cross (-442772331868971891 : ℤ) (3152519739159347200 : ℕ) none))
                      Certificate.outside))
                  Certificate.outside)
                Certificate.outside)))
          (Certificate.splitX (-384 : ℤ)
            (Certificate.cross (0 : ℤ) (1 : ℕ) none)
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                Certificate.outside
                Certificate.outside)
              (Certificate.splitX (-192 : ℤ)
                Certificate.outside
                (Certificate.splitY (1344 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    Certificate.outside
                    Certificate.outside)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (1440 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (1488 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (-168 : ℤ)
                            (Certificate.splitY (1512 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (-180 : ℤ)
                                Certificate.outside
                                Certificate.outside))
                            Certificate.outside))
                        Certificate.outside))
                    Certificate.outside))))))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            Certificate.inside
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (576 : ℤ)
                Certificate.inside
                (Certificate.splitY (-1344 : ℤ)
                  (Certificate.splitX (672 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-1440 : ℤ)
                      (Certificate.splitX (720 : ℤ)
                        (Certificate.splitY (-1488 : ℤ)
                          (Certificate.splitX (696 : ℤ)
                            (Certificate.splitY (-1512 : ℤ)
                              (Certificate.splitX (684 : ℤ)
                                Certificate.inside
                                Certificate.inside)
                              Certificate.inside)
                            Certificate.inside)
                          Certificate.inside)
                        Certificate.inside)
                      Certificate.inside))
                  Certificate.inside))
              Certificate.inside))
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-480 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (240 : ℤ)
                        Certificate.inside
                        Certificate.inside))
                    (Certificate.splitY (-480 : ℤ)
                      Certificate.inside
                      Certificate.inside))))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (96 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (144 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-48 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (168 : ℤ)
                            (Certificate.cross (-52563480838980641 : ℤ) (337769972052787200 : ℕ) none)
                            (Certificate.cross (-409665301402043 : ℤ) (1759218604441600 : ℕ) none)))))))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (336 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (360 : ℤ)
                            (Certificate.cross (-1509878245320736649 : ℤ) (21617278211378380800 : ℕ) none)
                            (Certificate.cross (-1520299331316469 : ℤ) (14073748835532800 : ℕ) none))))))
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (264 : ℤ)
                            (Certificate.cross (-16501655432510460817 : ℤ) (172938225691027046400 : ℕ) none)
                            (Certificate.cross (-1177904911959176753 : ℤ) (7205759403792793600 : ℕ) none))))
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (-48 : ℤ)
                          (Certificate.cross (-88190578023174944567 : ℤ) (461168601842738790400 : ℕ) none)
                          (Certificate.cross (-69303229889929627 : ℤ) (253327479039590400 : ℕ) none))
                        (Certificate.cross (-14502058425830469 : ℤ) (49258120924364800 : ℕ) none)))
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (312 : ℤ)
                            (Certificate.cross (-131534431322539900661 : ℤ) (1383505805528216371200 : ℕ) none)
                            (Certificate.splitY (-168 : ℤ)
                              (Certificate.cross (-122976095939056661411 : ℤ) (1383505805528216371200 : ℕ) none)
                              (Certificate.cross (-65094683120229314567 : ℤ) (461168601842738790400 : ℕ) none)))
                          (Certificate.cross (-25500083218604139149 : ℤ) (129703669268270284800 : ℕ) none))
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.cross (-335967148327271891 : ℤ) (2026619832316723200 : ℕ) none)
                          Certificate.outside))
                      Certificate.outside)))))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                      (Certificate.splitX (432 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.cross (-16157012956006529567 : ℤ) (461168601842738790400 : ℕ) none)
                          (Certificate.cross (-2082599064535577503 : ℤ) (16212958658533785600 : ℕ) none))
                        (Certificate.cross (-442772331868971891 : ℤ) (3152519739159347200 : ℕ) none)))
                    (Certificate.cross (-107405698253609377 : ℤ) (675539944105574400 : ℕ) none))
                  Certificate.outside)
                Certificate.outside))))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)
              (Certificate.splitX (960 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  Certificate.outside)))
            (Certificate.splitY (-384 : ℤ)
              Certificate.outside
              (Certificate.splitX (1344 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (1248 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)))
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (1440 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (1488 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (1512 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (-168 : ℤ)
                              (Certificate.splitX (1524 : ℤ)
                                Certificate.outside
                                (Certificate.splitY (-180 : ℤ)
                                  Certificate.outside
                                  Certificate.outside))
                              Certificate.outside))
                          Certificate.outside))
                      Certificate.outside)))))))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.splitX (48 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (48 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (72 : ℤ)
                            (Certificate.cross (-43384532170620851317 : ℤ) (172938225691027046400 : ℕ) none)
                            (Certificate.splitY (72 : ℤ)
                              (Certificate.cross (-43384532170620851317 : ℤ) (172938225691027046400 : ℕ) none)
                              (Certificate.cross (-2203947916608168503 : ℤ) (7205759403792793600 : ℕ) none)))))
                      (Certificate.splitX (48 : ℤ)
                        (Certificate.splitY (144 : ℤ)
                          (Certificate.splitX (24 : ℤ)
                            (Certificate.cross (-269125000915994131661 : ℤ) (1383505805528216371200 : ℕ) none)
                            (Certificate.cross (-130669835012580996317 : ℤ) (461168601842738790400 : ℕ) none))
                          (Certificate.cross (-5204470789292263003 : ℤ) (16212958658533785600 : ℕ) none))
                        (Certificate.splitY (144 : ℤ)
                          (Certificate.cross (-45647024808559626149 : ℤ) (129703669268270284800 : ℕ) none)
                          Certificate.outside)))
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.splitX (144 : ℤ)
                        (Certificate.splitY (48 : ℤ)
                          (Certificate.splitX (120 : ℤ)
                            (Certificate.cross (-318392773799987732411 : ℤ) (1383505805528216371200 : ℕ) none)
                            (Certificate.splitY (24 : ℤ)
                              (Certificate.cross (-269125000915994131661 : ℤ) (1383505805528216371200 : ℕ) none)
                              (Certificate.cross (-130669835012580996317 : ℤ) (461168601842738790400 : ℕ) none)))
                          (Certificate.cross (-45647024808559626149 : ℤ) (129703669268270284800 : ℕ) none))
                        (Certificate.cross (-1205278818694191891 : ℤ) (3152519739159347200 : ℕ) none))
                      Certificate.outside))
                  Certificate.outside)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (360 : ℤ)
                            (Certificate.splitY (360 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (360 : ℤ)
                              Certificate.outside
                              Certificate.outside))))))))
              (Certificate.splitX (192 : ℤ)
                Certificate.outside
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (336 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      Certificate.outside))
                  Certificate.outside)))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (432 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside))
                    Certificate.outside))
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  Certificate.outside))
              Certificate.outside))
          Certificate.outside)
        Certificate.outside)],
    ![
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (-1152 : ℤ)
            (Certificate.splitY (-1152 : ℤ)
              Certificate.inside
              (Certificate.splitX (-1344 : ℤ)
                Certificate.inside
                (Certificate.splitY (-960 : ℤ)
                  (Certificate.splitX (-1248 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-1056 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  Certificate.inside)))
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (-960 : ℤ)
                (Certificate.splitY (-1344 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-1056 : ℤ)
                    Certificate.inside
                    Certificate.inside))
                Certificate.inside)
              (Certificate.splitX (-960 : ℤ)
                (Certificate.splitY (-960 : ℤ)
                  (Certificate.splitX (-1056 : ℤ)
                    (Certificate.splitY (-1056 : ℤ)
                      (Certificate.splitX (-1104 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-1104 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-1080 : ℤ)
                            Certificate.inside
                            (Certificate.splitY (-1080 : ℤ)
                              Certificate.inside
                              Certificate.inside))))
                      (Certificate.splitX (-1104 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-1008 : ℤ)
                          (Certificate.splitX (-1080 : ℤ)
                            Certificate.inside
                            Certificate.inside)
                          Certificate.inside)))
                    (Certificate.splitY (-1056 : ℤ)
                      (Certificate.splitX (-1008 : ℤ)
                        (Certificate.splitY (-1104 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-1032 : ℤ)
                            (Certificate.splitY (-1080 : ℤ)
                              Certificate.inside
                              Certificate.inside)
                            Certificate.inside))
                        Certificate.inside)
                      Certificate.inside))
                  Certificate.inside)
                Certificate.inside)))
          Certificate.inside)
        (Certificate.splitY (-768 : ℤ)
          Certificate.inside
          (Certificate.splitX (-384 : ℤ)
            Certificate.inside
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.inside
                        Certificate.inside)
                      Certificate.inside)))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-144 : ℤ)
                        Certificate.inside
                        Certificate.inside))
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  Certificate.inside)))))),
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              Certificate.inside
              Certificate.inside)
            (Certificate.splitY (384 : ℤ)
              Certificate.inside
              Certificate.inside))
          (Certificate.cross (0 : ℤ) (1 : ℕ) none))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-480 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-432 : ℤ)
                        Certificate.inside
                        Certificate.inside)
                      Certificate.inside))))
              (Certificate.cross (0 : ℤ) (1 : ℕ) none))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    Certificate.inside)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (336 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-2146954142441157 : ℤ) (28147497671065600 : ℕ) none))))))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-48 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (144 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-675396139767879 : ℤ) (3518437208883200 : ℕ) none)))))
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-1856073028395819009 : ℤ) (14411518807585587200 : ℕ) none)))
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          (Certificate.splitX (-168 : ℤ)
                            (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                            (Certificate.cross (-102767825502492594951 : ℤ) (922337203685477580800 : ℕ) none))
                          (Certificate.splitX (-168 : ℤ)
                            (Certificate.cross (-3277272335019684759 : ℤ) (27922317689697075200 : ℕ) none)
                            Certificate.outside))
                        (Certificate.splitY (336 : ℤ)
                          (Certificate.splitX (-120 : ℤ)
                            (Certificate.cross (-2102484596745527227233 : ℤ) (14296226657124902502400 : ℕ) none)
                            Certificate.outside)
                          Certificate.outside)))
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-48 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.cross (-139429550943426984951 : ℤ) (922337203685477580800 : ℕ) none)
                          (Certificate.cross (-3009430149543060639 : ℤ) (14411518807585587200 : ℕ) none))
                        (Certificate.cross (-36639881366103657 : ℤ) (133700613937561600 : ℕ) none))
                      Certificate.outside))))
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.cross (-13367642622398452947 : ℤ) (331464932574468505600 : ℕ) none)
                        (Certificate.cross (-1015028904735346923 : ℤ) (8556839292003942400 : ℕ) none))
                      Certificate.outside))
                  Certificate.outside)
                Certificate.outside)))
          (Certificate.splitX (-384 : ℤ)
            (Certificate.cross (0 : ℤ) (1 : ℕ) none)
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                Certificate.outside
                Certificate.outside)
              (Certificate.splitX (-192 : ℤ)
                Certificate.outside
                (Certificate.splitY (1344 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (1440 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (1488 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (-168 : ℤ)
                            (Certificate.splitY (1512 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (-180 : ℤ)
                                Certificate.outside
                                Certificate.outside))
                            Certificate.outside))
                        Certificate.outside))
                    Certificate.outside))))))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            Certificate.inside
            Certificate.inside)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-480 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (240 : ℤ)
                        Certificate.inside
                        Certificate.inside))
                    Certificate.inside)))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    Certificate.inside)
                  (Certificate.splitX (96 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (144 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-48 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-675396139767879 : ℤ) (3518437208883200 : ℕ) none))))))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (336 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-2146954142441157 : ℤ) (28147497671065600 : ℕ) none)))))
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-1856073028395819009 : ℤ) (14411518807585587200 : ℕ) none)))
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (-48 : ℤ)
                          (Certificate.cross (-139429550943426984951 : ℤ) (922337203685477580800 : ℕ) none)
                          (Certificate.cross (-162370745042684631 : ℤ) (647392446434508800 : ℕ) none))
                        (Certificate.splitY (-48 : ℤ)
                          (Certificate.cross (-3009430149543060639 : ℤ) (14411518807585587200 : ℕ) none)
                          Certificate.outside)))
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (312 : ℤ)
                            (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                            (Certificate.cross (-102767825502492594951 : ℤ) (922337203685477580800 : ℕ) none))
                          (Certificate.splitX (312 : ℤ)
                            (Certificate.cross (-286574446993069164951 : ℤ) (1787028332140612812800 : ℕ) none)
                            Certificate.outside))
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (360 : ℤ)
                            (Certificate.cross (-1906763739497467963983 : ℤ) (14296226657124902502400 : ℕ) none)
                            Certificate.outside)
                          Certificate.outside))
                      Certificate.outside)))))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                      (Certificate.splitX (432 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                          (Certificate.cross (-4394011930731156759 : ℤ) (41433116571808563200 : ℕ) none))
                        (Certificate.cross (-1015028904735346923 : ℤ) (8556839292003942400 : ℕ) none)))
                    (Certificate.cross (-15401829374469993 : ℤ) (112589990684262400 : ℕ) none))
                  Certificate.outside)
                Certificate.outside))))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)
              (Certificate.splitX (960 : ℤ)
                Certificate.outside
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  Certificate.outside)))
            (Certificate.splitY (-384 : ℤ)
              Certificate.outside
              (Certificate.splitX (1344 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (1440 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (1488 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (1512 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (-168 : ℤ)
                              (Certificate.splitX (1524 : ℤ)
                                Certificate.outside
                                (Certificate.splitY (-180 : ℤ)
                                  Certificate.outside
                                  Certificate.outside))
                              Certificate.outside))
                          Certificate.outside))
                      Certificate.outside)))))))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.splitX (48 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (48 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (72 : ℤ)
                            (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                            (Certificate.splitY (72 : ℤ)
                              (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                              (Certificate.cross (-3954804292402304259 : ℤ) (14411518807585587200 : ℕ) none)))))
                      (Certificate.splitX (48 : ℤ)
                        (Certificate.splitY (144 : ℤ)
                          (Certificate.splitX (24 : ℤ)
                            (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                            (Certificate.cross (-229163681250129771201 : ℤ) (922337203685477580800 : ℕ) none))
                          (Certificate.cross (-536649043671771033 : ℤ) (1801439850948198400 : ℕ) none))
                        (Certificate.splitY (144 : ℤ)
                          (Certificate.splitX (72 : ℤ)
                            (Certificate.cross (-4254201638301016209483 : ℤ) (14296226657124902502400 : ℕ) none)
                            Certificate.outside)
                          Certificate.outside)))
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.splitX (144 : ℤ)
                        (Certificate.splitY (48 : ℤ)
                          (Certificate.splitX (120 : ℤ)
                            (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                            (Certificate.cross (-229163681250129771201 : ℤ) (922337203685477580800 : ℕ) none))
                          (Certificate.splitX (120 : ℤ)
                            (Certificate.splitY (72 : ℤ)
                              (Certificate.cross (-15796123376868962212989 : ℤ) (59029581035870565171200 : ℕ) none)
                              Certificate.outside)
                            Certificate.outside))
                        (Certificate.splitY (48 : ℤ)
                          (Certificate.cross (-536649043671771033 : ℤ) (1801439850948198400 : ℕ) none)
                          Certificate.outside))
                      Certificate.outside))
                  Certificate.outside)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (336 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (336 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (360 : ℤ)
                            (Certificate.splitY (360 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (360 : ℤ)
                              Certificate.outside
                              Certificate.outside))))))))
              (Certificate.splitX (192 : ℤ)
                Certificate.outside
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (336 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      Certificate.outside))
                  Certificate.outside)))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (432 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside))
                    Certificate.outside))
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  Certificate.outside))
              Certificate.outside))
          Certificate.outside)
        Certificate.outside)],
    ![
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (-1152 : ℤ)
            Certificate.inside
            (Certificate.splitY (-1152 : ℤ)
              Certificate.inside
              (Certificate.splitX (-960 : ℤ)
                Certificate.inside
                (Certificate.splitY (-960 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-864 : ℤ)
                    (Certificate.splitY (-864 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-912 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-816 : ℤ)
                          Certificate.inside
                          Certificate.inside)))
                    (Certificate.splitY (-864 : ℤ)
                      (Certificate.splitX (-816 : ℤ)
                        Certificate.inside
                        Certificate.inside)
                      (Certificate.splitX (-816 : ℤ)
                        (Certificate.splitY (-816 : ℤ)
                          (Certificate.splitX (-840 : ℤ)
                            (Certificate.splitY (-840 : ℤ)
                              Certificate.inside
                              Certificate.inside)
                            (Certificate.splitY (-840 : ℤ)
                              Certificate.inside
                              Certificate.inside))
                          Certificate.inside)
                        Certificate.inside)))))))
          (Certificate.splitX (-1152 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-1344 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  Certificate.inside))
              Certificate.inside)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-960 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                Certificate.inside)
              Certificate.inside)))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                Certificate.inside
                Certificate.inside)
              (Certificate.splitX (-576 : ℤ)
                (Certificate.splitY (-960 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                Certificate.inside))
            Certificate.inside)
          (Certificate.splitX (-384 : ℤ)
            Certificate.inside
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.inside
                      Certificate.inside)))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  Certificate.inside)))))),
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              Certificate.inside
              Certificate.inside)
            (Certificate.splitY (384 : ℤ)
              Certificate.inside
              Certificate.inside))
          (Certificate.cross (0 : ℤ) (1 : ℕ) none))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                Certificate.inside
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-480 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (288 : ℤ)
                      Certificate.inside
                      Certificate.inside))))
              (Certificate.cross (0 : ℤ) (1 : ℕ) none))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    Certificate.inside)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.inside
                        (Certificate.cross (-557437578006907 : ℤ) (14073748835532800 : ℕ) none)))))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      (Certificate.cross (-164195428082129 : ℤ) (1759218604441600 : ℕ) none)))
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.cross (-300320500006776509 : ℤ) (7205759403792793600 : ℕ) none)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          (Certificate.cross (-27246457647862117451 : ℤ) (461168601842738790400 : ℕ) none)
                          (Certificate.splitX (-168 : ℤ)
                            (Certificate.cross (-2117771974731816509 : ℤ) (20716558285904281600 : ℕ) none)
                            (Certificate.cross (-29128118948835667 : ℤ) (225179981368524800 : ℕ) none)))
                        (Certificate.splitY (336 : ℤ)
                          (Certificate.splitX (-120 : ℤ)
                            (Certificate.cross (-1300825697820330042733 : ℤ) (10606877842382992179200 : ℕ) none)
                            (Certificate.cross (-42217391139943089697 : ℤ) (273818857344126156800 : ℕ) none))
                          Certificate.outside)))
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-48 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.cross (-19832256064706875451 : ℤ) (461168601842738790400 : ℕ) none)
                          (Certificate.cross (-50550243943007465197 : ℤ) (273818857344126156800 : ℕ) none))
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.cross (-121700921451479381 : ℤ) (534802455750246400 : ℕ) none)
                          Certificate.outside))
                      Certificate.outside))))
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.cross (-5624645943591802447 : ℤ) (273818857344126156800 : ℕ) none)
                        (Certificate.cross (-826305067432511923 : ℤ) (7656119366529843200 : ℕ) none))
                      Certificate.outside))
                  Certificate.outside)
                Certificate.outside)))
          (Certificate.splitX (-384 : ℤ)
            (Certificate.cross (0 : ℤ) (1 : ℕ) none)
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                Certificate.outside
                Certificate.outside)
              (Certificate.splitX (-192 : ℤ)
                Certificate.outside
                (Certificate.splitY (1344 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    Certificate.outside
                    Certificate.outside)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (1440 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (1488 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (-168 : ℤ)
                            (Certificate.splitY (1512 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (-180 : ℤ)
                                Certificate.outside
                                Certificate.outside))
                            Certificate.outside))
                        Certificate.outside))
                    Certificate.outside))))))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            Certificate.inside
            Certificate.inside)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-480 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    Certificate.inside)))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  (Certificate.splitX (96 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.inside
                      (Certificate.cross (-164195428082129 : ℤ) (1759218604441600 : ℕ) none))))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (336 : ℤ)
                        Certificate.inside
                        (Certificate.cross (-557437578006907 : ℤ) (14073748835532800 : ℕ) none))))
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.cross (-300320500006776509 : ℤ) (7205759403792793600 : ℕ) none)
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (-48 : ℤ)
                          (Certificate.cross (-19832256064706875451 : ℤ) (461168601842738790400 : ℕ) none)
                          (Certificate.cross (-121700921451479381 : ℤ) (534802455750246400 : ℕ) none))
                        (Certificate.splitY (-48 : ℤ)
                          (Certificate.cross (-50550243943007465197 : ℤ) (273818857344126156800 : ℕ) none)
                          Certificate.outside)))
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.cross (-27246457647862117451 : ℤ) (461168601842738790400 : ℕ) none)
                          (Certificate.splitX (312 : ℤ)
                            (Certificate.cross (-173845085441304154451 : ℤ) (1325859730297874022400 : ℕ) none)
                            (Certificate.cross (-42217391139943089697 : ℤ) (273818857344126156800 : ℕ) none)))
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (360 : ℤ)
                            (Certificate.splitY (-168 : ℤ)
                              (Certificate.cross (-1743967367259168378239 : ℤ) (29514790517935282585600 : ℕ) none)
                              (Certificate.cross (-1209847697775442060483 : ℤ) (10606877842382992179200 : ℕ) none))
                            (Certificate.cross (-29128118948835667 : ℤ) (225179981368524800 : ℕ) none))
                          Certificate.outside))
                      Certificate.outside)))))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                      (Certificate.splitX (432 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                          (Certificate.cross (-3244470210316880759 : ℤ) (34227357168015769600 : ℕ) none))
                        (Certificate.cross (-826305067432511923 : ℤ) (7656119366529843200 : ℕ) none)))
                    (Certificate.cross (-226271452552667381 : ℤ) (1801439850948198400 : ℕ) none))
                  Certificate.outside)
                Certificate.outside))))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)
              (Certificate.splitX (960 : ℤ)
                Certificate.outside
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  Certificate.outside)))
            (Certificate.splitY (-384 : ℤ)
              Certificate.outside
              (Certificate.splitX (1344 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (1248 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)))
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (1440 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (1488 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (1512 : ℤ)
                            (Certificate.splitY (-168 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (-168 : ℤ)
                              (Certificate.splitX (1524 : ℤ)
                                Certificate.outside
                                (Certificate.splitY (-180 : ℤ)
                                  Certificate.outside
                                  Certificate.outside))
                              Certificate.outside))
                          Certificate.outside))
                      Certificate.outside)))))))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.splitX (48 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (48 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (72 : ℤ)
                            Certificate.inside
                            (Certificate.cross (-1677962460942059759 : ℤ) (7205759403792793600 : ℕ) none))))
                      (Certificate.splitX (48 : ℤ)
                        (Certificate.splitY (144 : ℤ)
                          (Certificate.cross (-86410056240021591701 : ℤ) (461168601842738790400 : ℕ) none)
                          (Certificate.splitX (24 : ℤ)
                            (Certificate.cross (-37787336076221701447 : ℤ) (165732466287234252800 : ℕ) none)
                            (Certificate.cross (-9561044700124838759 : ℤ) (34227357168015769600 : ℕ) none)))
                        (Certificate.splitY (144 : ℤ)
                          (Certificate.splitX (72 : ℤ)
                            (Certificate.splitY (120 : ℤ)
                              (Certificate.cross (-6517786139350377863489 : ℤ) (29514790517935282585600 : ℕ) none)
                              (Certificate.cross (-2947721043469887056983 : ℤ) (10606877842382992179200 : ℕ) none))
                            (Certificate.cross (-85908790714217084197 : ℤ) (273818857344126156800 : ℕ) none))
                          Certificate.outside)))
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.splitX (144 : ℤ)
                        (Certificate.splitY (48 : ℤ)
                          (Certificate.cross (-86410056240021591701 : ℤ) (461168601842738790400 : ℕ) none)
                          (Certificate.splitX (120 : ℤ)
                            (Certificate.splitY (72 : ℤ)
                              (Certificate.cross (-6517786139350377863489 : ℤ) (29514790517935282585600 : ℕ) none)
                              (Certificate.cross (-384077879932076572451 : ℤ) (1325859730297874022400 : ℕ) none))
                            (Certificate.cross (-85908790714217084197 : ℤ) (273818857344126156800 : ℕ) none)))
                        (Certificate.splitY (48 : ℤ)
                          (Certificate.splitX (168 : ℤ)
                            (Certificate.cross (-2716914351230431682233 : ℤ) (10606877842382992179200 : ℕ) none)
                            (Certificate.cross (-9561044700124838759 : ℤ) (34227357168015769600 : ℕ) none))
                          Certificate.outside))
                      Certificate.outside))
                  Certificate.outside)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (336 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (336 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (360 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (360 : ℤ)
                              Certificate.outside
                              Certificate.outside))))))))
              (Certificate.splitX (192 : ℤ)
                Certificate.outside
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (336 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (432 : ℤ)
                          Certificate.outside
                          Certificate.outside))
                      Certificate.outside))
                  Certificate.outside)))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (432 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside))
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      Certificate.outside)))
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  Certificate.outside))
              Certificate.outside))
          Certificate.outside)
        Certificate.outside)],
    ![
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (-1152 : ℤ)
            Certificate.inside
            (Certificate.splitY (-1152 : ℤ)
              Certificate.inside
              (Certificate.splitX (-960 : ℤ)
                Certificate.inside
                (Certificate.splitY (-960 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-864 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-864 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-816 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-816 : ℤ)
                          Certificate.inside
                          Certificate.inside))))))))
          (Certificate.splitX (-1152 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-1344 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  Certificate.inside))
              Certificate.inside)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-960 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.splitX (-864 : ℤ)
                    (Certificate.splitY (-672 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    (Certificate.splitY (-672 : ℤ)
                      (Certificate.splitX (-816 : ℤ)
                        (Certificate.splitY (-720 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        (Certificate.splitY (-720 : ℤ)
                          Certificate.inside
                          Certificate.inside))
                      Certificate.inside))
                  Certificate.inside))
              Certificate.inside)))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                Certificate.inside
                Certificate.inside)
              (Certificate.splitX (-576 : ℤ)
                (Certificate.splitY (-960 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-672 : ℤ)
                    (Certificate.splitY (-864 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-720 : ℤ)
                        (Certificate.splitY (-816 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        Certificate.inside))
                    Certificate.inside))
                Certificate.inside))
            Certificate.inside)
          (Certificate.splitX (-384 : ℤ)
            Certificate.inside
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.inside
                      Certificate.inside)))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  Certificate.inside)))))),
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              Certificate.inside
              Certificate.inside)
            (Certificate.splitY (384 : ℤ)
              Certificate.inside
              Certificate.inside))
          (Certificate.cross (0 : ℤ) (1 : ℕ) none))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                Certificate.inside
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-480 : ℤ)
                    Certificate.inside
                    Certificate.inside)))
              (Certificate.cross (0 : ℤ) (1 : ℕ) none))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    Certificate.inside)
                  Certificate.inside)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-168 : ℤ)
                            (Certificate.cross (-1280349761880628009 : ℤ) (13510798882111488000 : ℕ) none)
                            (Certificate.cross (-438897278228097173 : ℤ) (3377699720527872000 : ℕ) none)))
                        (Certificate.splitY (336 : ℤ)
                          (Certificate.splitX (-120 : ℤ)
                            (Certificate.cross (-748773988650882938483 : ℤ) (6917529027641081856000 : ℕ) none)
                            (Certificate.cross (-32551880126986277447 : ℤ) (216172782113783808000 : ℕ) none))
                          (Certificate.cross (-150620159680074631 : ℤ) (844424930131968000 : ℕ) none))))
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-48 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-38110834131675771947 : ℤ) (216172782113783808000 : ℕ) none))
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.cross (-46045549418750003 : ℤ) (211106232532992000 : ℕ) none)
                          (Certificate.cross (-13412060200892641 : ℤ) (52776558133248000 : ℕ) none)))
                      (Certificate.cross (-117236894577961 : ℤ) (412316860416000 : ℕ) none)))))
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                        (Certificate.cross (-730923881569696673 : ℤ) (6755399441055744000 : ℕ) none))
                      (Certificate.cross (-214421139408005131 : ℤ) (1688849860263936000 : ℕ) none)))
                  (Certificate.cross (-4074585252054377 : ℤ) (26388279066624000 : ℕ) none))
                (Certificate.cross (-73511363594709 : ℤ) (240518168576000 : ℕ) none))))
          (Certificate.splitX (-384 : ℤ)
            (Certificate.cross (0 : ℤ) (1 : ℕ) none)
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                Certificate.outside
                Certificate.outside)
              (Certificate.splitX (-192 : ℤ)
                Certificate.outside
                (Certificate.splitY (1344 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    Certificate.outside
                    Certificate.outside)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (1440 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (1488 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (-168 : ℤ)
                            (Certificate.splitY (1512 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (-180 : ℤ)
                                Certificate.outside
                                Certificate.outside))
                            Certificate.outside))
                        Certificate.outside))
                    Certificate.outside))))))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            Certificate.inside
            Certificate.inside)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (288 : ℤ)
                    Certificate.inside
                    Certificate.inside)))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  Certificate.inside)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (-48 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-46045549418750003 : ℤ) (211106232532992000 : ℕ) none))
                        (Certificate.splitY (-48 : ℤ)
                          (Certificate.cross (-38110834131675771947 : ℤ) (216172782113783808000 : ℕ) none)
                          (Certificate.cross (-13412060200892641 : ℤ) (52776558133248000 : ℕ) none))))
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (312 : ℤ)
                            (Certificate.cross (-94963399235768243701 : ℤ) (864691128455135232000 : ℕ) none)
                            (Certificate.cross (-32551880126986277447 : ℤ) (216172782113783808000 : ℕ) none)))
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (360 : ℤ)
                            (Certificate.cross (-727243458394084888733 : ℤ) (6917529027641081856000 : ℕ) none)
                            (Certificate.cross (-438897278228097173 : ℤ) (3377699720527872000 : ℕ) none))
                          (Certificate.cross (-150620159680074631 : ℤ) (844424930131968000 : ℕ) none)))
                      (Certificate.cross (-117236894577961 : ℤ) (412316860416000 : ℕ) none))))))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (432 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-2472666861152429509 : ℤ) (27021597764222976000 : ℕ) none))
                        (Certificate.cross (-730923881569696673 : ℤ) (6755399441055744000 : ℕ) none)))
                    (Certificate.cross (-214421139408005131 : ℤ) (1688849860263936000 : ℕ) none))
                  (Certificate.cross (-1644654879917563 : ℤ) (5497558138880000 : ℕ) none))
                (Certificate.cross (-7656114277390127 : ℤ) (26388279066624000 : ℕ) none)))))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)
              (Certificate.splitX (960 : ℤ)
                Certificate.outside
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  Certificate.outside)))
            (Certificate.splitY (-384 : ℤ)
              Certificate.outside
              (Certificate.splitX (1344 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (1248 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)))
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (1440 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (1392 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          Certificate.outside))
                      Certificate.outside)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (1488 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (1512 : ℤ)
                            (Certificate.splitY (-168 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (-168 : ℤ)
                              (Certificate.splitX (1524 : ℤ)
                                Certificate.outside
                                (Certificate.splitY (-180 : ℤ)
                                  Certificate.outside
                                  Certificate.outside))
                              Certificate.outside))
                          Certificate.outside))
                      Certificate.outside)))))))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (48 : ℤ)
                        (Certificate.splitY (144 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (24 : ℤ)
                            (Certificate.cross (-21778013071478072447 : ℤ) (108086391056891904000 : ℕ) none)
                            (Certificate.cross (-7382963031265243759 : ℤ) (27021597764222976000 : ℕ) none)))
                        (Certificate.splitY (144 : ℤ)
                          (Certificate.splitX (72 : ℤ)
                            (Certificate.cross (-1828427598195000158483 : ℤ) (6917529027641081856000 : ℕ) none)
                            (Certificate.splitY (120 : ℤ)
                              (Certificate.cross (-241632141791360908951 : ℤ) (864691128455135232000 : ℕ) none)
                              (Certificate.cross (-67191973733909017697 : ℤ) (216172782113783808000 : ℕ) none)))
                          (Certificate.cross (-2334281858933048423 : ℤ) (6755399441055744000 : ℕ) none))))
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.splitX (144 : ℤ)
                        (Certificate.splitY (48 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (120 : ℤ)
                            (Certificate.splitY (72 : ℤ)
                              Certificate.inside
                              (Certificate.cross (-241632141791360908951 : ℤ) (864691128455135232000 : ℕ) none))
                            (Certificate.cross (-67191973733909017697 : ℤ) (216172782113783808000 : ℕ) none)))
                        (Certificate.splitY (48 : ℤ)
                          (Certificate.splitX (168 : ℤ)
                            (Certificate.cross (-1636822735004363656733 : ℤ) (6917529027641081856000 : ℕ) none)
                            (Certificate.cross (-7382963031265243759 : ℤ) (27021597764222976000 : ℕ) none))
                          (Certificate.cross (-2334281858933048423 : ℤ) (6755399441055744000 : ℕ) none)))
                      (Certificate.cross (-727677993937652131 : ℤ) (1688849860263936000 : ℕ) none)))
                  (Certificate.cross (-343767171433666439 : ℤ) (703687441776640000 : ℕ) none))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.cross (-343767171433666439 : ℤ) (703687441776640000 : ℕ) none)
                  (Certificate.splitX (288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (336 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (336 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (360 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (360 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (372 : ℤ)
                                Certificate.outside
                                Certificate.outside)))))))))
              (Certificate.splitX (192 : ℤ)
                Certificate.outside
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.splitY (432 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (432 : ℤ)
                          (Certificate.splitX (360 : ℤ)
                            Certificate.outside
                            Certificate.outside)
                          Certificate.outside))
                      Certificate.outside))
                  Certificate.outside)))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (432 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (408 : ℤ)
                            (Certificate.splitY (360 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            Certificate.outside))
                        Certificate.outside))
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      Certificate.outside)))
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  Certificate.outside))
              Certificate.outside))
          Certificate.outside)
        (Certificate.splitY (768 : ℤ)
          Certificate.outside
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

end BerryEsseen.N2NeededIntegerPointwise11

#print axioms BerryEsseen.N2NeededIntegerPointwise11.powers_entries
#print axioms BerryEsseen.N2NeededIntegerPointwise11.powers_eq
#print axioms BerryEsseen.N2NeededIntegerPointwise11.checks
#print axioms BerryEsseen.N2NeededIntegerPointwise11.pointwise
