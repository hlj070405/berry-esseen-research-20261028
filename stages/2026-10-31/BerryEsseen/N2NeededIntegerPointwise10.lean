module

public import BerryEsseen.N2NeededIntegerData
public import BerryEsseen.N2IntegerPointwiseReplay

@[expose] public section

/-! 2026-10-29: integer power numerators and the unchanged original
rows055..059 closed trees. The entries equality is the semantic cache bridge.
No Bernstein coefficient or host closed flag is a premise. -/

namespace BerryEsseen.N2NeededIntegerPointwise10

open N2NeededData N2NeededIntegerData N2IntegerBernstein
  N2IntegerRectangleCertificate N2MajorantPolynomials

def rowIndex (j : Fin 5) : Fin 65 :=
  ⟨10 * 5 + j.val,
    lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (10 * 5)) (by decide)⟩

def signX : Fin 4 → ℚ := N2IntegerPointwiseReplay.signX
def signY : Fin 4 → ℚ := N2IntegerPointwiseReplay.signY

def powers : Fin 5 → Fin 4 → IntPower :=
  ![
    ![
      ![![(629094290080414 : ℤ), (-97731284228375 : ℤ), (-194461738835625 : ℤ), (-69823790360375 : ℤ)],
        ![(-97731284228375 : ℤ), (-246653584969375 : ℤ), (-38713737218250 : ℤ), (48744454743875 : ℤ)],
        ![(-194461738835625 : ℤ), (-38713737218250 : ℤ), (72737951472125 : ℤ), (6075867315875 : ℤ)],
        ![(-69823790360375 : ℤ), (48744454743875 : ℤ), (6075867315875 : ℤ), (-3244599313750 : ℤ)]],
      ![![(629094290080414 : ℤ), (-97731284228375 : ℤ), (-194461738835625 : ℤ), (59839412186625 : ℤ)],
        ![(-97731284228375 : ℤ), (-246653584969375 : ℤ), (-38713737218250 : ℤ), (65245530031375 : ℤ)],
        ![(-194461738835625 : ℤ), (-38713737218250 : ℤ), (72737951472125 : ℤ), (11020707444625 : ℤ)],
        ![(-69823790360375 : ℤ), (48744454743875 : ℤ), (6075867315875 : ℤ), (-5410439811000 : ℤ)]],
      ![![(629094290080414 : ℤ), (-97731284228375 : ℤ), (-194461738835625 : ℤ), (-69823790360375 : ℤ)],
        ![(-97731284228375 : ℤ), (-246653584969375 : ℤ), (-38713737218250 : ℤ), (48744454743875 : ℤ)],
        ![(-194461738835625 : ℤ), (-38713737218250 : ℤ), (72737951472125 : ℤ), (6075867315875 : ℤ)],
        ![(59839412186625 : ℤ), (65245530031375 : ℤ), (11020707444625 : ℤ), (-5410439811000 : ℤ)]],
      ![![(629094290080414 : ℤ), (-97731284228375 : ℤ), (-194461738835625 : ℤ), (59839412186625 : ℤ)],
        ![(-97731284228375 : ℤ), (-246653584969375 : ℤ), (-38713737218250 : ℤ), (65245530031375 : ℤ)],
        ![(-194461738835625 : ℤ), (-38713737218250 : ℤ), (72737951472125 : ℤ), (11020707444625 : ℤ)],
        ![(59839412186625 : ℤ), (65245530031375 : ℤ), (11020707444625 : ℤ), (-9012324847250 : ℤ)]]],
    ![
      ![![(630100663644539 : ℤ), (-87223336854250 : ℤ), (-187518343022625 : ℤ), (-69533056102250 : ℤ)],
        ![(-87223336854250 : ℤ), (-240342758421875 : ℤ), (-49412938509375 : ℤ), (43495383507625 : ℤ)],
        ![(-187518343022625 : ℤ), (-49412938509375 : ℤ), (64585836866375 : ℤ), (7548431408250 : ℤ)],
        ![(-69533056102250 : ℤ), (43495383507625 : ℤ), (7548431408250 : ℤ), (-2344960105250 : ℤ)]],
      ![![(630100663644539 : ℤ), (-87223336854250 : ℤ), (-187518343022625 : ℤ), (55989227418500 : ℤ)],
        ![(-87223336854250 : ℤ), (-240342758421875 : ℤ), (-49412938509375 : ℤ), (65233096106375 : ℤ)],
        ![(-187518343022625 : ℤ), (-49412938509375 : ℤ), (64585836866375 : ℤ), (14135632743000 : ℤ)],
        ![(-69533056102250 : ℤ), (43495383507625 : ℤ), (7548431408250 : ℤ), (-4781582289500 : ℤ)]],
      ![![(630100663644539 : ℤ), (-87223336854250 : ℤ), (-187518343022625 : ℤ), (-69533056102250 : ℤ)],
        ![(-87223336854250 : ℤ), (-240342758421875 : ℤ), (-49412938509375 : ℤ), (43495383507625 : ℤ)],
        ![(-187518343022625 : ℤ), (-49412938509375 : ℤ), (64585836866375 : ℤ), (7548431408250 : ℤ)],
        ![(55989227418500 : ℤ), (65233096106375 : ℤ), (14135632743000 : ℤ), (-4781582289500 : ℤ)]],
      ![![(630100663644539 : ℤ), (-87223336854250 : ℤ), (-187518343022625 : ℤ), (55989227418500 : ℤ)],
        ![(-87223336854250 : ℤ), (-240342758421875 : ℤ), (-49412938509375 : ℤ), (65233096106375 : ℤ)],
        ![(-187518343022625 : ℤ), (-49412938509375 : ℤ), (64585836866375 : ℤ), (14135632743000 : ℤ)],
        ![(55989227418500 : ℤ), (65233096106375 : ℤ), (14135632743000 : ℤ), (-9707087154250 : ℤ)]]],
    ![
      ![![(622187939368539 : ℤ), (-66215435082625 : ℤ), (-170311560603375 : ℤ), (-69048109268375 : ℤ)],
        ![(-66215435082625 : ℤ), (-221151488664250 : ℤ), (-69708230093625 : ℤ), (33759239243375 : ℤ)],
        ![(-170311560603375 : ℤ), (-69708230093625 : ℤ), (46849692889750 : ℤ), (7967876512375 : ℤ)],
        ![(-69048109268375 : ℤ), (33759239243375 : ℤ), (7967876512375 : ℤ), (-1390795510125 : ℤ)]],
      ![![(622187939368539 : ℤ), (-66215435082625 : ℤ), (-170311560603375 : ℤ), (46948046719125 : ℤ)],
        ![(-66215435082625 : ℤ), (-221151488664250 : ℤ), (-69708230093625 : ℤ), (61843610701625 : ℤ)],
        ![(-170311560603375 : ℤ), (-69708230093625 : ℤ), (46849692889750 : ℤ), (18904674746125 : ℤ)],
        ![(-69048109268375 : ℤ), (33759239243375 : ℤ), (7967876512375 : ℤ), (-2740050203625 : ℤ)]],
      ![![(622187939368539 : ℤ), (-66215435082625 : ℤ), (-170311560603375 : ℤ), (-69048109268375 : ℤ)],
        ![(-66215435082625 : ℤ), (-221151488664250 : ℤ), (-69708230093625 : ℤ), (33759239243375 : ℤ)],
        ![(-170311560603375 : ℤ), (-69708230093625 : ℤ), (46849692889750 : ℤ), (7967876512375 : ℤ)],
        ![(46948046719125 : ℤ), (61843610701625 : ℤ), (18904674746125 : ℤ), (-2740050203625 : ℤ)]],
      ![![(622187939368539 : ℤ), (-66215435082625 : ℤ), (-170311560603375 : ℤ), (46948046719125 : ℤ)],
        ![(-66215435082625 : ℤ), (-221151488664250 : ℤ), (-69708230093625 : ℤ), (61843610701625 : ℤ)],
        ![(-170311560603375 : ℤ), (-69708230093625 : ℤ), (46849692889750 : ℤ), (18904674746125 : ℤ)],
        ![(46948046719125 : ℤ), (61843610701625 : ℤ), (18904674746125 : ℤ), (-5257338840625 : ℤ)]]],
    ![
      ![![(614318735777789 : ℤ), (-54074221246250 : ℤ), (-155245878002875 : ℤ), (-68659190419500 : ℤ)],
        ![(-54074221246250 : ℤ), (-209530951829125 : ℤ), (-86288562228500 : ℤ), (24305436168625 : ℤ)],
        ![(-155245878002875 : ℤ), (-86288562228500 : ℤ), (26185324467875 : ℤ), (8981561180375 : ℤ)],
        ![(-68659190419500 : ℤ), (24305436168625 : ℤ), (8981561180375 : ℤ), (-132524167375 : ℤ)]],
      ![![(614318735777789 : ℤ), (-54074221246250 : ℤ), (-155245878002875 : ℤ), (43244444679750 : ℤ)],
        ![(-54074221246250 : ℤ), (-209530951829125 : ℤ), (-86288562228500 : ℤ), (66298569298375 : ℤ)],
        ![(-155245878002875 : ℤ), (-86288562228500 : ℤ), (26185324467875 : ℤ), (27372347453875 : ℤ)],
        ![(-68659190419500 : ℤ), (24305436168625 : ℤ), (8981561180375 : ℤ), (-1304158907875 : ℤ)]],
      ![![(614318735777789 : ℤ), (-54074221246250 : ℤ), (-155245878002875 : ℤ), (-68659190419500 : ℤ)],
        ![(-54074221246250 : ℤ), (-209530951829125 : ℤ), (-86288562228500 : ℤ), (24305436168625 : ℤ)],
        ![(-155245878002875 : ℤ), (-86288562228500 : ℤ), (26185324467875 : ℤ), (8981561180375 : ℤ)],
        ![(43244444679750 : ℤ), (66298569298375 : ℤ), (27372347453875 : ℤ), (-1304158907875 : ℤ)]],
      ![![(614318735777789 : ℤ), (-54074221246250 : ℤ), (-155245878002875 : ℤ), (43244444679750 : ℤ)],
        ![(-54074221246250 : ℤ), (-209530951829125 : ℤ), (-86288562228500 : ℤ), (66298569298375 : ℤ)],
        ![(-155245878002875 : ℤ), (-86288562228500 : ℤ), (26185324467875 : ℤ), (27372347453875 : ℤ)],
        ![(43244444679750 : ℤ), (66298569298375 : ℤ), (27372347453875 : ℤ), (-12734154712875 : ℤ)]]],
    ![
      ![![(610865403321289 : ℤ), (-39340497454750 : ℤ), (-142147649695500 : ℤ), (-65955315338125 : ℤ)],
        ![(-39340497454750 : ℤ), (-186997429935000 : ℤ), (-92539220048125 : ℤ), (17516703276875 : ℤ)],
        ![(-142147649695500 : ℤ), (-92539220048125 : ℤ), (18375632261125 : ℤ), (7520071467375 : ℤ)],
        ![(-65955315338125 : ℤ), (17516703276875 : ℤ), (7520071467375 : ℤ), (-92177001250 : ℤ)]],
      ![![(610865403321289 : ℤ), (-39340497454750 : ℤ), (-142147649695500 : ℤ), (34870179175875 : ℤ)],
        ![(-39340497454750 : ℤ), (-186997429935000 : ℤ), (-92539220048125 : ℤ), (55193882900375 : ℤ)],
        ![(-142147649695500 : ℤ), (-92539220048125 : ℤ), (18375632261125 : ℤ), (24012312254125 : ℤ)],
        ![(-65955315338125 : ℤ), (17516703276875 : ℤ), (7520071467375 : ℤ), (-204811633750 : ℤ)]],
      ![![(610865403321289 : ℤ), (-39340497454750 : ℤ), (-142147649695500 : ℤ), (-65955315338125 : ℤ)],
        ![(-39340497454750 : ℤ), (-186997429935000 : ℤ), (-92539220048125 : ℤ), (17516703276875 : ℤ)],
        ![(-142147649695500 : ℤ), (-92539220048125 : ℤ), (18375632261125 : ℤ), (7520071467375 : ℤ)],
        ![(34870179175875 : ℤ), (55193882900375 : ℤ), (24012312254125 : ℤ), (-204811633750 : ℤ)]],
      ![![(610865403321289 : ℤ), (-39340497454750 : ℤ), (-142147649695500 : ℤ), (34870179175875 : ℤ)],
        ![(-39340497454750 : ℤ), (-186997429935000 : ℤ), (-92539220048125 : ℤ), (55193882900375 : ℤ)],
        ![(-142147649695500 : ℤ), (-92539220048125 : ℤ), (18375632261125 : ℤ), (24012312254125 : ℤ)],
        ![(34870179175875 : ℤ), (55193882900375 : ℤ), (24012312254125 : ℤ), (-431363542250 : ℤ)]]]]

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
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-216 : ℤ)
                            Certificate.inside
                            Certificate.inside)))))
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.inside
                      Certificate.inside)
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
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        Certificate.inside))
                    Certificate.inside)
                  Certificate.inside)))))),
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-1344 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-1440 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-1488 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-1512 : ℤ)
                            (Certificate.splitY (360 : ℤ)
                              (Certificate.splitX (-1524 : ℤ)
                                (Certificate.splitY (348 : ℤ)
                                  Certificate.inside
                                  Certificate.inside)
                                (Certificate.splitY (348 : ℤ)
                                  Certificate.inside
                                  Certificate.inside))
                              Certificate.inside)
                            (Certificate.splitY (360 : ℤ)
                              Certificate.inside
                              Certificate.inside)))
                        (Certificate.splitY (336 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-1464 : ℤ)
                            (Certificate.splitY (360 : ℤ)
                              Certificate.inside
                              Certificate.inside)
                            (Certificate.splitY (360 : ℤ)
                              Certificate.inside
                              Certificate.inside)))))
                    (Certificate.splitY (288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-1392 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.inside
                          Certificate.inside)))))
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-1248 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-1296 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.inside
                          Certificate.inside)))
                    (Certificate.splitY (288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-1200 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.inside
                          Certificate.inside))))))
              Certificate.inside)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-960 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-1056 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-1104 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.inside
                          Certificate.inside)))
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-1008 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          Certificate.inside))
                      Certificate.inside)))
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-864 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-912 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-936 : ℤ)
                            (Certificate.splitY (264 : ℤ)
                              Certificate.inside
                              Certificate.inside)
                            (Certificate.splitY (264 : ℤ)
                              Certificate.inside
                              Certificate.inside)))
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-888 : ℤ)
                            (Certificate.splitY (264 : ℤ)
                              Certificate.inside
                              Certificate.inside)
                            (Certificate.splitY (264 : ℤ)
                              Certificate.inside
                              Certificate.inside))))
                      Certificate.inside)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-816 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-840 : ℤ)
                            (Certificate.splitY (264 : ℤ)
                              Certificate.inside
                              Certificate.inside)
                            (Certificate.splitY (264 : ℤ)
                              Certificate.inside
                              Certificate.inside)))
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.splitX (-792 : ℤ)
                            Certificate.inside
                            (Certificate.splitY (216 : ℤ)
                              Certificate.inside
                              Certificate.inside))
                          (Certificate.splitX (-792 : ℤ)
                            (Certificate.splitY (264 : ℤ)
                              Certificate.inside
                              Certificate.inside)
                            Certificate.inside)))
                      Certificate.inside))))
              Certificate.inside))
          (Certificate.cross (0 : ℤ) (1 : ℕ) none))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-672 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  (Certificate.splitX (-672 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-720 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.splitX (-744 : ℤ)
                            (Certificate.splitY (216 : ℤ)
                              Certificate.inside
                              Certificate.inside)
                            (Certificate.splitY (216 : ℤ)
                              Certificate.inside
                              Certificate.inside))
                          Certificate.inside)
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.splitX (-696 : ℤ)
                            (Certificate.splitY (216 : ℤ)
                              Certificate.inside
                              Certificate.inside)
                            Certificate.inside)
                          Certificate.inside))
                      Certificate.inside)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-624 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        Certificate.inside)
                      Certificate.inside)))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-480 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    Certificate.inside)
                  Certificate.inside))
              (Certificate.cross (0 : ℤ) (1 : ℕ) none))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-216 : ℤ)
                            Certificate.inside
                            (Certificate.cross (-81779363744054387 : ℤ) (337769972052787200 : ℕ) none))))
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          (Certificate.cross (-13742504249528367947 : ℤ) (86469112845513523200 : ℕ) none)
                          (Certificate.cross (-548695344717413899 : ℤ) (2364389804369510400 : ℕ) none))
                        (Certificate.splitY (336 : ℤ)
                          (Certificate.splitX (-216 : ℤ)
                            (Certificate.cross (-407926073509127750701 : ℤ) (1556444031219243417600 : ℕ) none)
                            (Certificate.cross (-2844771178072644721 : ℤ) (9457559217478041600 : ℕ) none))
                          Certificate.outside)))))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                      (Certificate.cross (-4998397635691129 : ℤ) (15832967439974400 : ℕ) none)))
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.cross (-12001124010000929447 : ℤ) (86469112845513523200 : ℕ) none)
                          (Certificate.cross (-5728594348452717317 : ℤ) (18915118434956083200 : ℕ) none))
                        (Certificate.cross (-2778988097943003923 : ℤ) (8106479329266892800 : ℕ) none))
                      Certificate.outside)
                    Certificate.outside)))
              (Certificate.splitX (-192 : ℤ)
                (Certificate.cross (-40412010094502883 : ℤ) (102034679057612800 : ℕ) none)
                Certificate.outside)))
          (Certificate.splitX (-384 : ℤ)
            (Certificate.cross (0 : ℤ) (1 : ℕ) none)
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (960 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (1056 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (1104 : ℤ)
                          (Certificate.splitX (-216 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (1080 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (-204 : ℤ)
                                Certificate.outside
                                Certificate.outside)))
                          (Certificate.splitX (-216 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (1128 : ℤ)
                              (Certificate.splitX (-204 : ℤ)
                                Certificate.outside
                                Certificate.outside)
                              (Certificate.splitX (-204 : ℤ)
                                Certificate.outside
                                Certificate.outside))))))))
                (Certificate.splitY (960 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    Certificate.outside
                    Certificate.outside)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (1056 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    Certificate.outside)))
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (1344 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (1248 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (1200 : ℤ)
                          (Certificate.splitX (-216 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (1176 : ℤ)
                              (Certificate.splitX (-204 : ℤ)
                                Certificate.outside
                                Certificate.outside)
                              Certificate.outside))
                          (Certificate.splitX (-216 : ℤ)
                            Certificate.outside
                            Certificate.outside)))
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (1296 : ℤ)
                          (Certificate.splitX (-216 : ℤ)
                            Certificate.outside
                            Certificate.outside)
                          Certificate.outside))))
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (1440 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      Certificate.outside)))
                Certificate.outside))))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                (Certificate.splitY (-1344 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-1440 : ℤ)
                      (Certificate.splitX (336 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-1488 : ℤ)
                          (Certificate.splitX (360 : ℤ)
                            (Certificate.splitY (-1512 : ℤ)
                              (Certificate.splitX (348 : ℤ)
                                Certificate.inside
                                Certificate.inside)
                              Certificate.inside)
                            Certificate.inside)
                          (Certificate.splitX (360 : ℤ)
                            Certificate.inside
                            Certificate.inside)))
                      (Certificate.splitX (336 : ℤ)
                        Certificate.inside
                        Certificate.inside)))
                  (Certificate.splitX (288 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-1248 : ℤ)
                      (Certificate.splitX (336 : ℤ)
                        Certificate.inside
                        Certificate.inside)
                      (Certificate.splitX (336 : ℤ)
                        Certificate.inside
                        Certificate.inside)))))
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                (Certificate.splitY (-960 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-1056 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (240 : ℤ)
                        Certificate.inside
                        Certificate.inside))
                    (Certificate.splitY (-1056 : ℤ)
                      (Certificate.splitX (336 : ℤ)
                        Certificate.inside
                        Certificate.inside)
                      Certificate.inside))
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-864 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-912 : ℤ)
                          (Certificate.splitX (264 : ℤ)
                            Certificate.inside
                            Certificate.inside)
                          (Certificate.splitX (264 : ℤ)
                            Certificate.inside
                            Certificate.inside)))
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (-816 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (216 : ℤ)
                            Certificate.inside
                            Certificate.inside))
                        (Certificate.splitY (-816 : ℤ)
                          (Certificate.splitX (264 : ℤ)
                            Certificate.inside
                            Certificate.inside)
                          (Certificate.splitX (264 : ℤ)
                            Certificate.inside
                            Certificate.inside))))
                    Certificate.inside))))
            Certificate.inside)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-672 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  (Certificate.splitX (96 : ℤ)
                    Certificate.inside
                    Certificate.inside))
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-672 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (-720 : ℤ)
                          (Certificate.splitX (216 : ℤ)
                            Certificate.inside
                            Certificate.inside)
                          (Certificate.splitX (216 : ℤ)
                            Certificate.inside
                            Certificate.inside))
                        Certificate.inside)
                      (Certificate.splitX (240 : ℤ)
                        Certificate.inside
                        Certificate.inside))
                    Certificate.inside)
                  Certificate.inside))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                      (Certificate.cross (-4998397635691129 : ℤ) (15832967439974400 : ℕ) none))))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (240 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (264 : ℤ)
                            Certificate.inside
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.inside
                              (Certificate.cross (-81779363744054387 : ℤ) (337769972052787200 : ℕ) none))))))
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.cross (-13742504249528367947 : ℤ) (86469112845513523200 : ℕ) none)
                          (Certificate.splitX (312 : ℤ)
                            (Certificate.splitY (-216 : ℤ)
                              (Certificate.cross (-1277783300103251875733 : ℤ) (5534023222112865484800 : ℕ) none)
                              (Certificate.cross (-13737095816588868143 : ℤ) (48638875975601356800 : ℕ) none))
                            (Certificate.cross (-2844771178072644721 : ℤ) (9457559217478041600 : ℕ) none)))
                        (Certificate.cross (-20582462910184141 : ℤ) (63331869759897600 : ℕ) none))))
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.cross (-12001124010000929447 : ℤ) (86469112845513523200 : ℕ) none)
                          (Certificate.cross (-637115951284089649 : ℤ) (2364389804369510400 : ℕ) none))
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.cross (-5728594348452717317 : ℤ) (18915118434956083200 : ℕ) none)
                          Certificate.outside))
                      Certificate.outside)
                    Certificate.outside))))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)
              (Certificate.splitX (576 : ℤ)
                (Certificate.cross (-50004450810482133 : ℤ) (102034679057612800 : ℕ) none)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  Certificate.outside)))))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)
              (Certificate.splitX (960 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (864 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (1056 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1008 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside)))
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1104 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1080 : ℤ)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (1092 : ℤ)
                                Certificate.outside
                                (Certificate.splitY (-204 : ℤ)
                                  Certificate.outside
                                  Certificate.outside)))))
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1128 : ℤ)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (1116 : ℤ)
                                (Certificate.splitY (-204 : ℤ)
                                  Certificate.outside
                                  Certificate.outside)
                                (Certificate.splitY (-204 : ℤ)
                                  Certificate.outside
                                  Certificate.outside)))
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (1140 : ℤ)
                                (Certificate.splitY (-204 : ℤ)
                                  Certificate.outside
                                  Certificate.outside)
                                (Certificate.splitY (-204 : ℤ)
                                  Certificate.outside
                                  Certificate.outside))))))))
                  (Certificate.splitX (1056 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    Certificate.outside))))
            (Certificate.splitY (-384 : ℤ)
              Certificate.outside
              (Certificate.splitX (1344 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (1248 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1200 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1176 : ℤ)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (1164 : ℤ)
                                (Certificate.splitY (-204 : ℤ)
                                  Certificate.outside
                                  Certificate.outside)
                                Certificate.outside))
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside)))
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1224 : ℤ)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside)))))
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1296 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1272 : ℤ)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            Certificate.outside))
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside))))
                  Certificate.outside)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (1440 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1392 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside)))
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      Certificate.outside))
                  Certificate.outside)))))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.cross (-3295214031005419399 : ℤ) (7430939385161318400 : ℕ) none)
                    Certificate.outside)
                  Certificate.outside)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (240 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (336 : ℤ)
                          Certificate.outside
                          Certificate.outside)))
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (336 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          (Certificate.splitX (312 : ℤ)
                            (Certificate.splitY (312 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (312 : ℤ)
                              Certificate.outside
                              Certificate.outside))
                          Certificate.outside)
                        Certificate.outside)))))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    Certificate.outside
                    Certificate.outside)
                  Certificate.outside)))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    Certificate.outside))
                Certificate.outside)
              Certificate.outside))
          Certificate.outside)
        Certificate.outside)],
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
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-216 : ℤ)
                            Certificate.inside
                            Certificate.inside)))))
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.inside
                      Certificate.inside)
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
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        Certificate.inside))
                    Certificate.inside)
                  Certificate.inside)))))),
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-1344 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-1440 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-1488 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-1512 : ℤ)
                            (Certificate.splitY (360 : ℤ)
                              Certificate.inside
                              (Certificate.splitX (-1524 : ℤ)
                                (Certificate.splitY (372 : ℤ)
                                  (Certificate.splitX (-1530 : ℤ)
                                    (Certificate.splitY (366 : ℤ)
                                      Certificate.inside
                                      Certificate.inside)
                                    Certificate.inside)
                                  Certificate.inside)
                                (Certificate.splitY (372 : ℤ)
                                  Certificate.inside
                                  Certificate.inside)))
                            (Certificate.splitY (360 : ℤ)
                              Certificate.inside
                              Certificate.inside)))
                        (Certificate.splitY (336 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-1464 : ℤ)
                            (Certificate.splitY (360 : ℤ)
                              Certificate.inside
                              Certificate.inside)
                            (Certificate.splitY (360 : ℤ)
                              Certificate.inside
                              Certificate.inside)))))
                    (Certificate.splitY (288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-1392 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.inside
                          Certificate.inside)))))
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-1248 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-1296 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.inside
                          Certificate.inside)))
                    (Certificate.splitY (288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-1200 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.inside
                          Certificate.inside))))))
              Certificate.inside)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-960 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-1056 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-1104 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.inside
                          Certificate.inside)))
                    (Certificate.splitY (288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-1008 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.inside
                          Certificate.inside)))))
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-864 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-912 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-888 : ℤ)
                            (Certificate.splitY (264 : ℤ)
                              Certificate.inside
                              Certificate.inside)
                            (Certificate.splitY (264 : ℤ)
                              Certificate.inside
                              Certificate.inside))))
                      Certificate.inside)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-816 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-840 : ℤ)
                            (Certificate.splitY (264 : ℤ)
                              Certificate.inside
                              Certificate.inside)
                            (Certificate.splitY (264 : ℤ)
                              Certificate.inside
                              Certificate.inside)))
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-792 : ℤ)
                            (Certificate.splitY (264 : ℤ)
                              Certificate.inside
                              Certificate.inside)
                            (Certificate.splitY (264 : ℤ)
                              (Certificate.splitX (-780 : ℤ)
                                Certificate.inside
                                (Certificate.splitY (252 : ℤ)
                                  Certificate.inside
                                  Certificate.inside))
                              Certificate.inside))))
                      Certificate.inside))))
              Certificate.inside))
          (Certificate.cross (0 : ℤ) (1 : ℕ) none))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-672 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-720 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.splitX (-744 : ℤ)
                            Certificate.inside
                            (Certificate.splitY (216 : ℤ)
                              Certificate.inside
                              Certificate.inside))
                          (Certificate.splitX (-744 : ℤ)
                            (Certificate.splitY (264 : ℤ)
                              (Certificate.splitX (-756 : ℤ)
                                (Certificate.splitY (252 : ℤ)
                                  Certificate.inside
                                  Certificate.inside)
                                Certificate.inside)
                              Certificate.inside)
                            Certificate.inside))
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.splitX (-696 : ℤ)
                            (Certificate.splitY (216 : ℤ)
                              Certificate.inside
                              Certificate.inside)
                            (Certificate.splitY (216 : ℤ)
                              Certificate.inside
                              Certificate.inside))
                          Certificate.inside))
                      Certificate.inside)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-624 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        Certificate.inside)
                      Certificate.inside)))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-480 : ℤ)
                    Certificate.inside
                    Certificate.inside)
                  Certificate.inside))
              (Certificate.cross (0 : ℤ) (1 : ℕ) none))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.inside
                        (Certificate.cross (-15196270103781387 : ℤ) (112589990684262400 : ℕ) none))
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.cross (-191085145139008137 : ℤ) (957014920816230400 : ℕ) none)
                        (Certificate.splitY (336 : ℤ)
                          (Certificate.splitX (-216 : ℤ)
                            (Certificate.cross (-503056882253223625527 : ℤ) (2190550858753009254400 : ℕ) none)
                            (Certificate.cross (-124980959763896763 : ℤ) (450359962737049600 : ℕ) none))
                          Certificate.outside)))))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                      (Certificate.cross (-535450124137563 : ℤ) (1759218604441600 : ℕ) none)))
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                          (Certificate.splitX (-168 : ℤ)
                            (Certificate.cross (-68795685187570148769 : ℤ) (273818857344126156800 : ℕ) none)
                            (Certificate.cross (-17204056736812912893 : ℤ) (61248954932238745600 : ℕ) none)))
                        (Certificate.cross (-4691433007735332471 : ℤ) (14411518807585587200 : ℕ) none))
                      Certificate.outside)
                    Certificate.outside)))
              (Certificate.splitX (-192 : ℤ)
                (Certificate.cross (-5249758601145269 : ℤ) (14073748835532800 : ℕ) none)
                Certificate.outside)))
          (Certificate.splitX (-384 : ℤ)
            (Certificate.cross (0 : ℤ) (1 : ℕ) none)
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (960 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (1056 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (1104 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (-216 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (1128 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (-204 : ℤ)
                                Certificate.outside
                                Certificate.outside))))))))
                (Certificate.splitY (960 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    Certificate.outside
                    Certificate.outside)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (1056 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    Certificate.outside)))
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (1344 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (1248 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (1200 : ℤ)
                          (Certificate.splitX (-216 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (1176 : ℤ)
                              (Certificate.splitX (-204 : ℤ)
                                Certificate.outside
                                Certificate.outside)
                              (Certificate.splitX (-204 : ℤ)
                                Certificate.outside
                                Certificate.outside)))
                          (Certificate.splitX (-216 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (1224 : ℤ)
                              (Certificate.splitX (-204 : ℤ)
                                Certificate.outside
                                Certificate.outside)
                              Certificate.outside))))
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (1296 : ℤ)
                          (Certificate.splitX (-216 : ℤ)
                            Certificate.outside
                            Certificate.outside)
                          (Certificate.splitX (-216 : ℤ)
                            Certificate.outside
                            Certificate.outside)))))
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (1440 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        Certificate.outside))))
                Certificate.outside))))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                (Certificate.splitY (-1344 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-1440 : ℤ)
                      (Certificate.splitX (336 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-1488 : ℤ)
                          (Certificate.splitX (360 : ℤ)
                            Certificate.inside
                            (Certificate.splitY (-1512 : ℤ)
                              (Certificate.splitX (372 : ℤ)
                                (Certificate.splitY (-1524 : ℤ)
                                  (Certificate.splitX (366 : ℤ)
                                    Certificate.inside
                                    Certificate.inside)
                                  Certificate.inside)
                                Certificate.inside)
                              Certificate.inside))
                          (Certificate.splitX (360 : ℤ)
                            Certificate.inside
                            Certificate.inside)))
                      (Certificate.splitX (336 : ℤ)
                        Certificate.inside
                        Certificate.inside)))
                  (Certificate.splitX (288 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-1248 : ℤ)
                      (Certificate.splitX (336 : ℤ)
                        Certificate.inside
                        Certificate.inside)
                      (Certificate.splitX (336 : ℤ)
                        Certificate.inside
                        Certificate.inside)))))
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                (Certificate.splitY (-960 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-1056 : ℤ)
                      (Certificate.splitX (336 : ℤ)
                        Certificate.inside
                        Certificate.inside)
                      (Certificate.splitX (336 : ℤ)
                        Certificate.inside
                        Certificate.inside)))
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-864 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-912 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (264 : ℤ)
                            Certificate.inside
                            Certificate.inside)))
                      (Certificate.splitX (240 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-816 : ℤ)
                          (Certificate.splitX (264 : ℤ)
                            Certificate.inside
                            Certificate.inside)
                          (Certificate.splitX (264 : ℤ)
                            (Certificate.splitY (-792 : ℤ)
                              Certificate.inside
                              (Certificate.splitX (252 : ℤ)
                                Certificate.inside
                                Certificate.inside))
                            Certificate.inside))))
                    Certificate.inside))))
            Certificate.inside)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (96 : ℤ)
                    Certificate.inside
                    Certificate.inside))
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-672 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (-720 : ℤ)
                          (Certificate.splitX (216 : ℤ)
                            Certificate.inside
                            Certificate.inside)
                          (Certificate.splitX (216 : ℤ)
                            Certificate.inside
                            Certificate.inside))
                        (Certificate.splitY (-720 : ℤ)
                          (Certificate.splitX (264 : ℤ)
                            (Certificate.splitY (-744 : ℤ)
                              (Certificate.splitX (252 : ℤ)
                                Certificate.inside
                                Certificate.inside)
                              Certificate.inside)
                            Certificate.inside)
                          Certificate.inside))
                      (Certificate.splitX (240 : ℤ)
                        Certificate.inside
                        Certificate.inside))
                    Certificate.inside)
                  Certificate.inside))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                      (Certificate.cross (-535450124137563 : ℤ) (1759218604441600 : ℕ) none))))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (240 : ℤ)
                        Certificate.inside
                        (Certificate.cross (-15196270103781387 : ℤ) (112589990684262400 : ℕ) none)))
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                          (Certificate.splitX (312 : ℤ)
                            (Certificate.splitY (-216 : ℤ)
                              (Certificate.cross (-420663003069706825341 : ℤ) (3689348814741910323200 : ℕ) none)
                              (Certificate.cross (-8731375620776472393 : ℤ) (34227357168015769600 : ℕ) none))
                            (Certificate.cross (-124980959763896763 : ℤ) (450359962737049600 : ℕ) none)))
                        (Certificate.cross (-8514293128762383 : ℤ) (28147497671065600 : ℕ) none))))
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                          (Certificate.cross (-15026022564882787893 : ℤ) (61248954932238745600 : ℕ) none))
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (264 : ℤ)
                            (Certificate.cross (-494750404172653413777 : ℤ) (2190550858753009254400 : ℕ) none)
                            (Certificate.cross (-17204056736812912893 : ℤ) (61248954932238745600 : ℕ) none))
                          Certificate.outside))
                      Certificate.outside)
                    Certificate.outside))))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.cross (-10006966185673443 : ℤ) (28147497671065600 : ℕ) none)
                  Certificate.outside)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  Certificate.outside)))))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)
              (Certificate.splitX (960 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (864 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (1056 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1104 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1128 : ℤ)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (1140 : ℤ)
                                (Certificate.splitY (-204 : ℤ)
                                  Certificate.outside
                                  Certificate.outside)
                                (Certificate.splitY (-204 : ℤ)
                                  Certificate.outside
                                  Certificate.outside))))))))
                  (Certificate.splitX (1056 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)))))
            (Certificate.splitY (-384 : ℤ)
              Certificate.outside
              (Certificate.splitX (1344 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (1248 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1200 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1176 : ℤ)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (1164 : ℤ)
                                (Certificate.splitY (-204 : ℤ)
                                  Certificate.outside
                                  Certificate.outside)
                                (Certificate.splitY (-204 : ℤ)
                                  Certificate.outside
                                  Certificate.outside)))
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (1188 : ℤ)
                                (Certificate.splitY (-204 : ℤ)
                                  Certificate.outside
                                  Certificate.outside)
                                (Certificate.splitY (-204 : ℤ)
                                  Certificate.outside
                                  Certificate.outside)))))
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1224 : ℤ)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (1212 : ℤ)
                                (Certificate.splitY (-204 : ℤ)
                                  Certificate.outside
                                  Certificate.outside)
                                (Certificate.splitY (-204 : ℤ)
                                  Certificate.outside
                                  Certificate.outside)))
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside)))))
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1296 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1272 : ℤ)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside)))
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1320 : ℤ)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            Certificate.outside)))))
                  Certificate.outside)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (1440 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1392 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside)))
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1488 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside)))
                  Certificate.outside)))))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.cross (-8765689765211656317 : ℤ) (28823037615171174400 : ℕ) none)
                      Certificate.outside)
                    Certificate.outside)
                  Certificate.outside)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (240 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (336 : ℤ)
                          Certificate.outside
                          Certificate.outside)))
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (336 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          (Certificate.splitX (312 : ℤ)
                            (Certificate.splitY (312 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (312 : ℤ)
                              Certificate.outside
                              Certificate.outside))
                          Certificate.outside)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.outside
                          Certificate.outside))))))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    Certificate.outside
                    Certificate.outside)
                  Certificate.outside)))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    Certificate.outside))
                Certificate.outside)
              Certificate.outside))
          Certificate.outside)
        Certificate.outside)],
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
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.inside
                          Certificate.inside))))
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.inside
                      Certificate.inside)
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
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        Certificate.inside))
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  Certificate.inside)))))),
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-1344 : ℤ)
                Certificate.inside
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-1248 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (288 : ℤ)
                      Certificate.inside
                      Certificate.inside))))
              (Certificate.splitX (-1344 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (-1440 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (-1488 : ℤ)
                        (Certificate.splitY (432 : ℤ)
                          (Certificate.splitX (-1512 : ℤ)
                            (Certificate.splitY (408 : ℤ)
                              Certificate.inside
                              (Certificate.splitX (-1524 : ℤ)
                                (Certificate.splitY (420 : ℤ)
                                  Certificate.inside
                                  Certificate.inside)
                                Certificate.inside))
                            (Certificate.splitY (408 : ℤ)
                              Certificate.inside
                              Certificate.inside))
                          Certificate.inside)
                        (Certificate.splitY (432 : ℤ)
                          Certificate.inside
                          Certificate.inside))
                      Certificate.inside)
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (-1392 : ℤ)
                        (Certificate.splitY (432 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        (Certificate.splitY (432 : ℤ)
                          Certificate.inside
                          Certificate.inside))
                      Certificate.inside))
                  Certificate.inside)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (-1248 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    Certificate.inside)
                  Certificate.inside)))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-960 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-1056 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.inside
                      Certificate.inside)))
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-864 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-912 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (336 : ℤ)
                          Certificate.inside
                          Certificate.inside)))
                    (Certificate.splitY (288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-816 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        Certificate.inside)))))
              Certificate.inside))
          (Certificate.cross (0 : ℤ) (1 : ℕ) none))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-672 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-720 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-744 : ℤ)
                            Certificate.inside
                            (Certificate.splitY (264 : ℤ)
                              Certificate.inside
                              Certificate.inside)))
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-696 : ℤ)
                            (Certificate.splitY (264 : ℤ)
                              Certificate.inside
                              Certificate.inside)
                            (Certificate.splitY (264 : ℤ)
                              Certificate.inside
                              Certificate.inside))))
                      Certificate.inside)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-624 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-648 : ℤ)
                            (Certificate.splitY (264 : ℤ)
                              Certificate.inside
                              Certificate.inside)
                            (Certificate.splitY (264 : ℤ)
                              Certificate.inside
                              Certificate.inside)))
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          Certificate.inside))
                      Certificate.inside)))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-480 : ℤ)
                    Certificate.inside
                    Certificate.inside)
                  (Certificate.splitX (-480 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-528 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        Certificate.inside)
                      Certificate.inside)
                    Certificate.inside)))
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
                        (Certificate.cross (-395017128199947673 : ℤ) (2927339757790822400 : ℕ) none)
                        (Certificate.splitY (336 : ℤ)
                          (Certificate.splitX (-216 : ℤ)
                            (Certificate.cross (-772657466673502853233 : ℤ) (5072854620270126694400 : ℕ) none)
                            (Certificate.splitY (312 : ℤ)
                              (Certificate.cross (-14840485119265618447 : ℤ) (79263353441720729600 : ℕ) none)
                              (Certificate.cross (-5172159311960529509 : ℤ) (23418718062326579200 : ℕ) none)))
                          (Certificate.cross (-24280556415820657 : ℤ) (98516241848729600 : ℕ) none))))))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      (Certificate.cross (-3406303773516629 : ℤ) (12314530231091200 : ℕ) none)))
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-168 : ℤ)
                            (Certificate.cross (-115538745074417029451 : ℤ) (634106827533765836800 : ℕ) none)
                            (Certificate.cross (-42927849505966594447 : ℤ) (187349744498612633600 : ℕ) none)))
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.cross (-36994892056997957947 : ℤ) (187349744498612633600 : ℕ) none)
                          (Certificate.cross (-14185776295155921509 : ℤ) (50440315826549555200 : ℕ) none)))
                      (Certificate.cross (-557930861675501381 : ℤ) (1632554864921804800 : ℕ) none))
                    (Certificate.cross (-183012640599233 : ℤ) (439804651110400 : ℕ) none))))
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.cross (-962229660805922923 : ℤ) (13060438919374438400 : ℕ) none)
                    (Certificate.cross (-741535805198333381 : ℤ) (2476979795053772800 : ℕ) none))
                  Certificate.outside)
                Certificate.outside)))
          (Certificate.splitX (-384 : ℤ)
            (Certificate.cross (0 : ℤ) (1 : ℕ) none)
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                Certificate.outside
                (Certificate.splitY (960 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    Certificate.outside
                    Certificate.outside)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (1056 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (-144 : ℤ)
                        Certificate.outside
                        Certificate.outside))
                    Certificate.outside)))
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (1344 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (1248 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (1200 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (-216 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (1224 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (-204 : ℤ)
                                Certificate.outside
                                Certificate.outside)))))
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (1296 : ℤ)
                          (Certificate.splitX (-216 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (1272 : ℤ)
                              (Certificate.splitX (-204 : ℤ)
                                Certificate.outside
                                Certificate.outside)
                              (Certificate.splitX (-204 : ℤ)
                                Certificate.outside
                                (Certificate.splitY (1284 : ℤ)
                                  (Certificate.splitX (-198 : ℤ)
                                    Certificate.outside
                                    Certificate.outside)
                                  (Certificate.splitX (-198 : ℤ)
                                    Certificate.outside
                                    Certificate.outside)))))
                          (Certificate.splitX (-216 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (1320 : ℤ)
                              (Certificate.splitX (-204 : ℤ)
                                Certificate.outside
                                Certificate.outside)
                              (Certificate.splitX (-204 : ℤ)
                                Certificate.outside
                                Certificate.outside)))))))
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (1440 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (1392 : ℤ)
                          (Certificate.splitX (-216 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (1368 : ℤ)
                              (Certificate.splitX (-204 : ℤ)
                                Certificate.outside
                                Certificate.outside)
                              Certificate.outside))
                          (Certificate.splitX (-216 : ℤ)
                            Certificate.outside
                            Certificate.outside)))
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        Certificate.outside))))
                (Certificate.splitY (1344 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (1248 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      Certificate.outside)
                    Certificate.outside)
                  Certificate.outside)))))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                (Certificate.splitY (-1344 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (288 : ℤ)
                    Certificate.inside
                    Certificate.inside)))
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                (Certificate.splitY (-960 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    Certificate.inside
                    Certificate.inside)
                  (Certificate.splitX (288 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-864 : ℤ)
                      (Certificate.splitX (336 : ℤ)
                        Certificate.inside
                        Certificate.inside)
                      (Certificate.splitX (336 : ℤ)
                        Certificate.inside
                        Certificate.inside))))))
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (-1344 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (-1440 : ℤ)
                      (Certificate.splitX (432 : ℤ)
                        (Certificate.splitY (-1488 : ℤ)
                          (Certificate.splitX (408 : ℤ)
                            Certificate.inside
                            (Certificate.splitY (-1512 : ℤ)
                              (Certificate.splitX (420 : ℤ)
                                Certificate.inside
                                Certificate.inside)
                              Certificate.inside))
                          Certificate.inside)
                        Certificate.inside)
                      (Certificate.splitX (432 : ℤ)
                        Certificate.inside
                        Certificate.inside))
                    Certificate.inside)
                  (Certificate.splitX (480 : ℤ)
                    Certificate.inside
                    Certificate.inside))
                Certificate.inside)
              Certificate.inside))
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (96 : ℤ)
                    Certificate.inside
                    Certificate.inside))
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-672 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-720 : ℤ)
                          (Certificate.splitX (264 : ℤ)
                            Certificate.inside
                            Certificate.inside)
                          (Certificate.splitX (264 : ℤ)
                            Certificate.inside
                            Certificate.inside)))
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (-624 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        (Certificate.splitY (-624 : ℤ)
                          (Certificate.splitX (264 : ℤ)
                            Certificate.inside
                            Certificate.inside)
                          Certificate.inside)))
                    Certificate.inside)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-480 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        Certificate.inside
                        Certificate.inside)
                      Certificate.inside)
                    Certificate.inside)))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (96 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.inside
                      (Certificate.cross (-3406303773516629 : ℤ) (12314530231091200 : ℕ) none))))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (312 : ℤ)
                            (Certificate.cross (-14840485119265618447 : ℤ) (79263353441720729600 : ℕ) none)
                            (Certificate.cross (-5172159311960529509 : ℤ) (23418718062326579200 : ℕ) none)))
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.cross (-395017128199947673 : ℤ) (2927339757790822400 : ℕ) none)
                          (Certificate.cross (-24280556415820657 : ℤ) (98516241848729600 : ℕ) none)))))
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-36994892056997957947 : ℤ) (187349744498612633600 : ℕ) none))
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (264 : ℤ)
                            (Certificate.cross (-751016088823771751983 : ℤ) (5072854620270126694400 : ℕ) none)
                            (Certificate.cross (-42927849505966594447 : ℤ) (187349744498612633600 : ℕ) none))
                          (Certificate.cross (-14185776295155921509 : ℤ) (50440315826549555200 : ℕ) none)))
                      (Certificate.cross (-77191607574300907 : ℤ) (204069358115225600 : ℕ) none))
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.cross (-557930861675501381 : ℤ) (1632554864921804800 : ℕ) none)
                      Certificate.outside)))))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.cross (-3625428035768257423 : ℤ) (13060438919374438400 : ℕ) none)
                    (Certificate.cross (-741535805198333381 : ℤ) (2476979795053772800 : ℕ) none))
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
                  (Certificate.splitX (864 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)))
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (1056 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (1104 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          Certificate.outside))
                      Certificate.outside)))))
            (Certificate.splitY (-384 : ℤ)
              Certificate.outside
              (Certificate.splitX (1344 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (1248 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1200 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1224 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (1236 : ℤ)
                                Certificate.outside
                                (Certificate.splitY (-204 : ℤ)
                                  Certificate.outside
                                  Certificate.outside)))))))
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1296 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1272 : ℤ)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (1260 : ℤ)
                                (Certificate.splitY (-204 : ℤ)
                                  Certificate.outside
                                  Certificate.outside)
                                (Certificate.splitY (-204 : ℤ)
                                  Certificate.outside
                                  Certificate.outside)))
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (1284 : ℤ)
                                (Certificate.splitY (-204 : ℤ)
                                  Certificate.outside
                                  (Certificate.splitX (1278 : ℤ)
                                    Certificate.outside
                                    (Certificate.splitY (-198 : ℤ)
                                      Certificate.outside
                                      Certificate.outside)))
                                (Certificate.splitY (-204 : ℤ)
                                  Certificate.outside
                                  (Certificate.splitX (1290 : ℤ)
                                    (Certificate.splitY (-198 : ℤ)
                                      Certificate.outside
                                      Certificate.outside)
                                    Certificate.outside))))))
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1320 : ℤ)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (1308 : ℤ)
                                (Certificate.splitY (-204 : ℤ)
                                  Certificate.outside
                                  Certificate.outside)
                                (Certificate.splitY (-204 : ℤ)
                                  Certificate.outside
                                  Certificate.outside)))
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (1332 : ℤ)
                                (Certificate.splitY (-204 : ℤ)
                                  Certificate.outside
                                  Certificate.outside)
                                (Certificate.splitY (-204 : ℤ)
                                  Certificate.outside
                                  Certificate.outside))))))))
                  (Certificate.splitX (1248 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (1200 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)
                    Certificate.outside))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (1440 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1392 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1368 : ℤ)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (1356 : ℤ)
                                (Certificate.splitY (-204 : ℤ)
                                  Certificate.outside
                                  Certificate.outside)
                                (Certificate.splitY (-204 : ℤ)
                                  Certificate.outside
                                  Certificate.outside)))
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside)))
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1416 : ℤ)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside)))))
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1488 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside))))
                  Certificate.outside)))))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.cross (-14415637787884010009 : ℤ) (50440315826549555200 : ℕ) none)
                      (Certificate.cross (-5448744861144299173 : ℤ) (13060438919374438400 : ℕ) none))
                    (Certificate.cross (-1229199613449036881 : ℤ) (2476979795053772800 : ℕ) none))
                  Certificate.outside)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (240 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (336 : ℤ)
                          Certificate.outside
                          Certificate.outside)))
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (336 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          (Certificate.splitX (312 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (312 : ℤ)
                              Certificate.outside
                              Certificate.outside))
                          (Certificate.splitX (312 : ℤ)
                            Certificate.outside
                            Certificate.outside))
                        (Certificate.splitY (336 : ℤ)
                          (Certificate.splitX (360 : ℤ)
                            (Certificate.splitY (312 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            Certificate.outside)
                          Certificate.outside))))))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    Certificate.outside
                    Certificate.outside)
                  Certificate.outside)))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    Certificate.outside))
                Certificate.outside)
              Certificate.outside))
          Certificate.outside)
        Certificate.outside)],
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
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.inside
                          Certificate.inside))))
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
                  (Certificate.splitX (-1440 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      (Certificate.splitX (-1488 : ℤ)
                        (Certificate.splitY (432 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-1512 : ℤ)
                            (Certificate.splitY (456 : ℤ)
                              Certificate.inside
                              (Certificate.splitX (-1524 : ℤ)
                                (Certificate.splitY (468 : ℤ)
                                  Certificate.inside
                                  Certificate.inside)
                                Certificate.inside))
                            Certificate.inside))
                        (Certificate.splitY (432 : ℤ)
                          Certificate.inside
                          Certificate.inside))
                      Certificate.inside)
                    (Certificate.splitY (480 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  Certificate.inside)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (-1248 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    (Certificate.splitY (480 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  Certificate.inside)))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-960 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-864 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-816 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (336 : ℤ)
                          Certificate.inside
                          Certificate.inside))))))
              (Certificate.splitX (-960 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (-1056 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    Certificate.inside)
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
                      (Certificate.splitX (-720 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.inside
                          Certificate.inside)))
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-624 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          Certificate.inside))
                      (Certificate.splitX (-624 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        Certificate.inside))))
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-480 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-528 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        Certificate.inside)
                      Certificate.inside)
                    Certificate.inside)))
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
                        (Certificate.cross (-65889011228128141 : ℤ) (675539944105574400 : ℕ) none)
                        (Certificate.splitY (336 : ℤ)
                          (Certificate.splitX (-216 : ℤ)
                            (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                            (Certificate.cross (-945396091909966253 : ℤ) (5404319552844595200 : ℕ) none))
                          (Certificate.cross (-5792426213473469 : ℤ) (28147497671065600 : ℕ) none))))))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-48 : ℤ)
                        (Certificate.cross (-709594847978924003 : ℤ) (5404319552844595200 : ℕ) none)
                        (Certificate.cross (-480797870103959 : ℤ) (1759218604441600 : ℕ) none))))
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-168 : ℤ)
                            (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                            (Certificate.cross (-7827171671202979399 : ℤ) (43234556422756761600 : ℕ) none)))
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.cross (-6844046953633340899 : ℤ) (43234556422756761600 : ℕ) none)
                          (Certificate.cross (-3549198449825766253 : ℤ) (14411518807585587200 : ℕ) none)))
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          (Certificate.splitX (-168 : ℤ)
                            (Certificate.cross (-96132579084375002901 : ℤ) (461168601842738790400 : ℕ) none)
                            Certificate.outside)
                          Certificate.outside)
                        Certificate.outside))
                    (Certificate.cross (-146601089794599 : ℤ) (384829069721600 : ℕ) none))))
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.cross (-228309428728378891 : ℤ) (4053239664633446400 : ℕ) none)
                    (Certificate.cross (-203002723724363877 : ℤ) (788129934789836800 : ℕ) none))
                  Certificate.outside)
                Certificate.outside)))
          (Certificate.splitX (-384 : ℤ)
            (Certificate.cross (0 : ℤ) (1 : ℕ) none)
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                Certificate.outside
                (Certificate.splitY (960 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (-96 : ℤ)
                    Certificate.outside
                    Certificate.outside)))
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (1344 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (1248 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (1296 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (-216 : ℤ)
                            Certificate.outside
                            Certificate.outside)))))
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (1440 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (1392 : ℤ)
                          (Certificate.splitX (-216 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (1368 : ℤ)
                              (Certificate.splitX (-204 : ℤ)
                                Certificate.outside
                                Certificate.outside)
                              (Certificate.splitX (-204 : ℤ)
                                Certificate.outside
                                Certificate.outside)))
                          (Certificate.splitX (-216 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (1416 : ℤ)
                              (Certificate.splitX (-204 : ℤ)
                                Certificate.outside
                                Certificate.outside)
                              (Certificate.splitX (-204 : ℤ)
                                Certificate.outside
                                Certificate.outside)))))
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (1488 : ℤ)
                          (Certificate.splitX (-216 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (1464 : ℤ)
                              (Certificate.splitX (-204 : ℤ)
                                Certificate.outside
                                Certificate.outside)
                              (Certificate.splitX (-204 : ℤ)
                                Certificate.outside
                                Certificate.outside)))
                          (Certificate.splitX (-216 : ℤ)
                            Certificate.outside
                            Certificate.outside))))))
                (Certificate.splitY (1344 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    Certificate.outside
                    Certificate.outside)
                  Certificate.outside)))))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-1152 : ℤ)
              Certificate.inside
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                (Certificate.splitY (-960 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (288 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-864 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (336 : ℤ)
                        Certificate.inside
                        Certificate.inside))))))
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (-1344 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (-1440 : ℤ)
                      (Certificate.splitX (432 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-1488 : ℤ)
                          (Certificate.splitX (456 : ℤ)
                            Certificate.inside
                            (Certificate.splitY (-1512 : ℤ)
                              (Certificate.splitX (468 : ℤ)
                                Certificate.inside
                                Certificate.inside)
                              Certificate.inside))
                          Certificate.inside))
                      Certificate.inside)
                    Certificate.inside)
                  (Certificate.splitX (480 : ℤ)
                    Certificate.inside
                    Certificate.inside))
                Certificate.inside)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (-960 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    Certificate.inside
                    Certificate.inside)
                  Certificate.inside)
                Certificate.inside)))
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-672 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (240 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-624 : ℤ)
                          Certificate.inside
                          Certificate.inside)))
                    (Certificate.splitY (-672 : ℤ)
                      (Certificate.splitX (336 : ℤ)
                        Certificate.inside
                        Certificate.inside)
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.splitY (-624 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        Certificate.inside)))
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-480 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        Certificate.inside
                        Certificate.inside)
                      Certificate.inside)
                    Certificate.inside)))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (96 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (144 : ℤ)
                        (Certificate.cross (-4968455901828751 : ℤ) (42221246506598400 : ℕ) none)
                        (Certificate.splitY (-48 : ℤ)
                          (Certificate.cross (-709594847978924003 : ℤ) (5404319552844595200 : ℕ) none)
                          (Certificate.cross (-480797870103959 : ℤ) (1759218604441600 : ℕ) none))))))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (312 : ℤ)
                            (Certificate.cross (-245369681392187399 : ℤ) (7205759403792793600 : ℕ) none)
                            (Certificate.splitY (-216 : ℤ)
                              (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                              (Certificate.cross (-945396091909966253 : ℤ) (5404319552844595200 : ℕ) none))))
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.cross (-65889011228128141 : ℤ) (675539944105574400 : ℕ) none)
                          (Certificate.cross (-5792426213473469 : ℤ) (28147497671065600 : ℕ) none)))))
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.cross (-6844046953633340899 : ℤ) (43234556422756761600 : ℕ) none)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (264 : ℤ)
                            (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                            (Certificate.cross (-7827171671202979399 : ℤ) (43234556422756761600 : ℕ) none))
                          (Certificate.cross (-3549198449825766253 : ℤ) (14411518807585587200 : ℕ) none)))
                      (Certificate.cross (-11194110700765547 : ℤ) (31665934879948800 : ℕ) none))
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (312 : ℤ)
                            (Certificate.cross (-1092662205416364202161 : ℤ) (5072854620270126694400 : ℕ) none)
                            Certificate.outside)
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)))))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.cross (-117433116919309753 : ℤ) (14411518807585587200 : ℕ) none)
                      (Certificate.cross (-956919898323390391 : ℤ) (4053239664633446400 : ℕ) none))
                    (Certificate.cross (-203002723724363877 : ℤ) (788129934789836800 : ℕ) none))
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
                  (Certificate.splitX (1056 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)))))
            (Certificate.splitY (-384 : ℤ)
              Certificate.outside
              (Certificate.splitX (1344 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (1248 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1296 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1320 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside))))))
                  (Certificate.splitX (1248 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (1440 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1392 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1368 : ℤ)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (1356 : ℤ)
                                (Certificate.splitY (-204 : ℤ)
                                  Certificate.outside
                                  Certificate.outside)
                                (Certificate.splitY (-204 : ℤ)
                                  Certificate.outside
                                  Certificate.outside)))
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (1380 : ℤ)
                                (Certificate.splitY (-204 : ℤ)
                                  Certificate.outside
                                  Certificate.outside)
                                (Certificate.splitY (-204 : ℤ)
                                  Certificate.outside
                                  Certificate.outside)))))
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1416 : ℤ)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (1404 : ℤ)
                                (Certificate.splitY (-204 : ℤ)
                                  Certificate.outside
                                  Certificate.outside)
                                (Certificate.splitY (-204 : ℤ)
                                  Certificate.outside
                                  Certificate.outside)))
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (1428 : ℤ)
                                (Certificate.splitY (-204 : ℤ)
                                  Certificate.outside
                                  Certificate.outside)
                                (Certificate.splitY (-204 : ℤ)
                                  Certificate.outside
                                  Certificate.outside)))))))
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1488 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1464 : ℤ)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (1452 : ℤ)
                                (Certificate.splitY (-204 : ℤ)
                                  Certificate.outside
                                  Certificate.outside)
                                (Certificate.splitY (-204 : ℤ)
                                  Certificate.outside
                                  Certificate.outside)))
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (1476 : ℤ)
                                (Certificate.splitY (-204 : ℤ)
                                  Certificate.outside
                                  Certificate.outside)
                                (Certificate.splitY (-204 : ℤ)
                                  Certificate.outside
                                  Certificate.outside)))))
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1512 : ℤ)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside))))))
                  Certificate.outside)))))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.splitX (48 : ℤ)
                        (Certificate.cross (-5384413220639880649 : ℤ) (43234556422756761600 : ℕ) none)
                        (Certificate.cross (-4382191327292182753 : ℤ) (14411518807585587200 : ℕ) none))
                      (Certificate.cross (-1679925700614070141 : ℤ) (4053239664633446400 : ℕ) none))
                    (Certificate.cross (-388321453193338377 : ℤ) (788129934789836800 : ℕ) none))
                  Certificate.outside)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (312 : ℤ)
                            Certificate.outside
                            Certificate.outside))
                        (Certificate.splitY (336 : ℤ)
                          (Certificate.splitX (360 : ℤ)
                            (Certificate.splitY (312 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            Certificate.outside)
                          Certificate.outside))))))
              (Certificate.splitX (192 : ℤ)
                Certificate.outside
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    Certificate.outside
                    Certificate.outside)
                  Certificate.outside)))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    Certificate.outside))
                Certificate.outside)
              Certificate.outside))
          Certificate.outside)
        Certificate.outside)],
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
                  (Certificate.splitX (-1440 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-1488 : ℤ)
                        (Certificate.splitY (528 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-1512 : ℤ)
                            (Certificate.splitY (552 : ℤ)
                              (Certificate.splitX (-1524 : ℤ)
                                (Certificate.splitY (540 : ℤ)
                                  Certificate.inside
                                  Certificate.inside)
                                Certificate.inside)
                              Certificate.inside)
                            Certificate.inside))
                        Certificate.inside))
                    (Certificate.splitY (480 : ℤ)
                      Certificate.inside
                      Certificate.inside))
                  Certificate.inside)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (-1248 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    Certificate.inside)
                  Certificate.inside)))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-960 : ℤ)
                Certificate.inside
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  Certificate.inside))
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
                      (Certificate.splitX (-624 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          Certificate.inside))
                      (Certificate.splitX (-624 : ℤ)
                        Certificate.inside
                        Certificate.inside))))
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-480 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-528 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-552 : ℤ)
                            (Certificate.splitY (264 : ℤ)
                              Certificate.inside
                              Certificate.inside)
                            Certificate.inside))
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          Certificate.inside))
                      Certificate.inside)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.inside
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
                        (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                        (Certificate.splitY (336 : ℤ)
                          (Certificate.cross (-535583212764349817 : ℤ) (4503599627370496000 : ℕ) none)
                          (Certificate.cross (-2946632574629633 : ℤ) (17592186044416000 : ℕ) none))))))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-48 : ℤ)
                        (Certificate.cross (-127539823192526567 : ℤ) (4503599627370496000 : ℕ) none)
                        (Certificate.cross (-2153150705386879 : ℤ) (8796093022208000 : ℕ) none))))
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.cross (-4631966845899947161 : ℤ) (36028797018963968000 : ℕ) none)
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.cross (-3039203169640308661 : ℤ) (36028797018963968000 : ℕ) none)
                          (Certificate.cross (-3920557714708121567 : ℤ) (18014398509481984000 : ℕ) none)))
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          (Certificate.splitX (-168 : ℤ)
                            (Certificate.cross (-996640051577171947429 : ℤ) (5764607523034234880000 : ℕ) none)
                            (Certificate.cross (-232233070343960641913 : ℤ) (1152921504606846976000 : ℕ) none))
                          Certificate.outside)
                        Certificate.outside))
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-48 : ℤ)
                        (Certificate.cross (-68946568203915250411 : ℤ) (252201579132747776000 : ℕ) none)
                        Certificate.outside)
                      Certificate.outside))))
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.cross (-83440773989635399 : ℤ) (5629499534213120000 : ℕ) none)
                    (Certificate.cross (-245164663216428503 : ℤ) (1125899906842624000 : ℕ) none))
                  Certificate.outside)
                Certificate.outside)))
          (Certificate.splitX (-384 : ℤ)
            (Certificate.cross (0 : ℤ) (1 : ℕ) none)
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                Certificate.outside
                (Certificate.splitY (960 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (-96 : ℤ)
                    Certificate.outside
                    Certificate.outside)))
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
                              (Certificate.splitX (-204 : ℤ)
                                Certificate.outside
                                Certificate.outside)
                              (Certificate.splitX (-204 : ℤ)
                                Certificate.outside
                                Certificate.outside))))))))
                (Certificate.splitY (1344 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (1248 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (-144 : ℤ)
                        Certificate.outside
                        Certificate.outside))
                    Certificate.outside)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (1440 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (1392 : ℤ)
                          (Certificate.splitX (-168 : ℤ)
                            Certificate.outside
                            Certificate.outside)
                          (Certificate.splitX (-168 : ℤ)
                            Certificate.outside
                            Certificate.outside))
                        Certificate.outside)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (1488 : ℤ)
                          (Certificate.splitX (-168 : ℤ)
                            Certificate.outside
                            Certificate.outside)
                          Certificate.outside)
                        Certificate.outside))
                    Certificate.outside))))))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-1152 : ℤ)
              Certificate.inside
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                Certificate.inside))
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (-1344 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-1440 : ℤ)
                      (Certificate.splitX (528 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-1488 : ℤ)
                          (Certificate.splitX (552 : ℤ)
                            (Certificate.splitY (-1512 : ℤ)
                              (Certificate.splitX (540 : ℤ)
                                Certificate.inside
                                Certificate.inside)
                              Certificate.inside)
                            Certificate.inside)
                          Certificate.inside))
                      Certificate.inside))
                  (Certificate.splitX (480 : ℤ)
                    Certificate.inside
                    Certificate.inside))
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
                    (Certificate.splitY (-672 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (240 : ℤ)
                        Certificate.inside
                        Certificate.inside))
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
                          (Certificate.splitX (264 : ℤ)
                            Certificate.inside
                            Certificate.inside)
                          Certificate.inside))
                      Certificate.inside)
                    Certificate.inside)))
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
                          (Certificate.cross (-127539823192526567 : ℤ) (4503599627370496000 : ℕ) none)
                          (Certificate.cross (-2153150705386879 : ℤ) (8796093022208000 : ℕ) none))))))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-535583212764349817 : ℤ) (4503599627370496000 : ℕ) none))
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                          (Certificate.cross (-2946632574629633 : ℤ) (17592186044416000 : ℕ) none)))))
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.cross (-3039203169640308661 : ℤ) (36028797018963968000 : ℕ) none)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.cross (-4631966845899947161 : ℤ) (36028797018963968000 : ℕ) none)
                          (Certificate.cross (-3920557714708121567 : ℤ) (18014398509481984000 : ℕ) none)))
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (-48 : ℤ)
                          (Certificate.cross (-264279735318863695913 : ℤ) (1152921504606846976000 : ℕ) none)
                          Certificate.outside)
                        Certificate.outside))
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (312 : ℤ)
                            (Certificate.splitY (-168 : ℤ)
                              (Certificate.cross (-2468549217296299172807 : ℤ) (18446744073709551616000 : ℕ) none)
                              (Certificate.cross (-1051364396905908062179 : ℤ) (5764607523034234880000 : ℕ) none))
                            (Certificate.cross (-232233070343960641913 : ℤ) (1152921504606846976000 : ℕ) none))
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)))))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                      (Certificate.cross (-1109750579198662399 : ℤ) (5629499534213120000 : ℕ) none))
                    (Certificate.cross (-245164663216428503 : ℤ) (1125899906842624000 : ℕ) none))
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
                  (Certificate.splitX (1056 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)))))
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
                      (Certificate.splitX (1296 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          Certificate.outside))
                      Certificate.outside)))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (1440 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1488 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1512 : ℤ)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (1500 : ℤ)
                                (Certificate.splitY (-204 : ℤ)
                                  Certificate.outside
                                  Certificate.outside)
                                (Certificate.splitY (-204 : ℤ)
                                  Certificate.outside
                                  Certificate.outside)))
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (1524 : ℤ)
                                (Certificate.splitY (-204 : ℤ)
                                  Certificate.outside
                                  Certificate.outside)
                                (Certificate.splitY (-204 : ℤ)
                                  Certificate.outside
                                  Certificate.outside))))))))
                  (Certificate.splitX (1440 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (1392 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (1368 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (-168 : ℤ)
                              Certificate.outside
                              Certificate.outside))
                          Certificate.outside)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (1416 : ℤ)
                            (Certificate.splitY (-168 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (-168 : ℤ)
                              Certificate.outside
                              Certificate.outside))
                          Certificate.outside))
                      Certificate.outside)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (1488 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (1464 : ℤ)
                            (Certificate.splitY (-168 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            Certificate.outside)
                          Certificate.outside)
                        Certificate.outside)
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
                        (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                        (Certificate.cross (-4961379132759255317 : ℤ) (18014398509481984000 : ℕ) none))
                      (Certificate.cross (-2194206701638463899 : ℤ) (5629499534213120000 : ℕ) none))
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.cross (-2194206701638463899 : ℤ) (5629499534213120000 : ℕ) none)
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
                          (Certificate.splitX (312 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (360 : ℤ)
                              Certificate.outside
                              Certificate.outside)))
                        (Certificate.splitY (336 : ℤ)
                          (Certificate.splitX (360 : ℤ)
                            Certificate.outside
                            Certificate.outside)
                          Certificate.outside))))))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    Certificate.outside)
                  Certificate.outside)))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    Certificate.outside))
                (Certificate.splitY (192 : ℤ)
                  Certificate.outside
                  Certificate.outside))
              Certificate.outside))
          Certificate.outside)
        Certificate.outside)]]

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

end BerryEsseen.N2NeededIntegerPointwise10

#print axioms BerryEsseen.N2NeededIntegerPointwise10.powers_entries
#print axioms BerryEsseen.N2NeededIntegerPointwise10.powers_eq
#print axioms BerryEsseen.N2NeededIntegerPointwise10.checks
#print axioms BerryEsseen.N2NeededIntegerPointwise10.pointwise
