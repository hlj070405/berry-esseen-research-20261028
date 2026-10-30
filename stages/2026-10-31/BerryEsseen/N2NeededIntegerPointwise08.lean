module

public import BerryEsseen.N2NeededIntegerData
public import BerryEsseen.N2IntegerPointwiseReplay

@[expose] public section

/-! 2026-10-29: integer power numerators and the unchanged original
rows045..049 closed trees. The entries equality is the semantic cache bridge.
No Bernstein coefficient or host closed flag is a premise. -/

namespace BerryEsseen.N2NeededIntegerPointwise08

open N2NeededData N2NeededIntegerData N2IntegerBernstein
  N2IntegerRectangleCertificate N2MajorantPolynomials

def rowIndex (j : Fin 5) : Fin 65 :=
  ⟨8 * 5 + j.val,
    lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (8 * 5)) (by decide)⟩

def signX : Fin 4 → ℚ := N2IntegerPointwiseReplay.signX
def signY : Fin 4 → ℚ := N2IntegerPointwiseReplay.signY

def powers : Fin 5 → Fin 4 → IntPower :=
  ![
    ![
      ![![(504973921517289 : ℤ), (-281268806465750 : ℤ), (-137283282800000 : ℤ), (-40919918106875 : ℤ)],
        ![(-281268806465750 : ℤ), (-198227309663875 : ℤ), (188804454174375 : ℤ), (96503618078625 : ℤ)],
        ![(-137283282800000 : ℤ), (188804454174375 : ℤ), (-2863301759125 : ℤ), (-46258550942375 : ℤ)],
        ![(-40919918106875 : ℤ), (96503618078625 : ℤ), (-46258550942375 : ℤ), (-19038529206500 : ℤ)]],
      ![![(504973921517289 : ℤ), (-281268806465750 : ℤ), (-137283282800000 : ℤ), (80088898219625 : ℤ)],
        ![(-281268806465750 : ℤ), (-198227309663875 : ℤ), (188804454174375 : ℤ), (3613574331125 : ℤ)],
        ![(-137283282800000 : ℤ), (188804454174375 : ℤ), (-2863301759125 : ℤ), (-4031242687875 : ℤ)],
        ![(-40919918106875 : ℤ), (96503618078625 : ℤ), (-46258550942375 : ℤ), (4003771061750 : ℤ)]],
      ![![(504973921517289 : ℤ), (-281268806465750 : ℤ), (-137283282800000 : ℤ), (-40919918106875 : ℤ)],
        ![(-281268806465750 : ℤ), (-198227309663875 : ℤ), (188804454174375 : ℤ), (96503618078625 : ℤ)],
        ![(-137283282800000 : ℤ), (188804454174375 : ℤ), (-2863301759125 : ℤ), (-46258550942375 : ℤ)],
        ![(80088898219625 : ℤ), (3613574331125 : ℤ), (-4031242687875 : ℤ), (4003771061750 : ℤ)]],
      ![![(504973921517289 : ℤ), (-281268806465750 : ℤ), (-137283282800000 : ℤ), (80088898219625 : ℤ)],
        ![(-281268806465750 : ℤ), (-198227309663875 : ℤ), (188804454174375 : ℤ), (3613574331125 : ℤ)],
        ![(-137283282800000 : ℤ), (188804454174375 : ℤ), (-2863301759125 : ℤ), (-4031242687875 : ℤ)],
        ![(80088898219625 : ℤ), (3613574331125 : ℤ), (-4031242687875 : ℤ), (-840858775000 : ℤ)]]],
    ![
      ![![(535041122672789 : ℤ), (-269915285196125 : ℤ), (-161128922761750 : ℤ), (-43876416461750 : ℤ)],
        ![(-269915285196125 : ℤ), (-210791415856125 : ℤ), (168598442860625 : ℤ), (87909569855875 : ℤ)],
        ![(-161128922761750 : ℤ), (168598442860625 : ℤ), (29644348912500 : ℤ), (-34159998645875 : ℤ)],
        ![(-43876416461750 : ℤ), (87909569855875 : ℤ), (-34159998645875 : ℤ), (-6460753648125 : ℤ)]],
      ![![(535041122672789 : ℤ), (-269915285196125 : ℤ), (-161128922761750 : ℤ), (83725236724500 : ℤ)],
        ![(-269915285196125 : ℤ), (-210791415856125 : ℤ), (168598442860625 : ℤ), (12058405109125 : ℤ)],
        ![(-161128922761750 : ℤ), (168598442860625 : ℤ), (29644348912500 : ℤ), (-9336083713125 : ℤ)],
        ![(-43876416461750 : ℤ), (87909569855875 : ℤ), (-34159998645875 : ℤ), (1267760404375 : ℤ)]],
      ![![(535041122672789 : ℤ), (-269915285196125 : ℤ), (-161128922761750 : ℤ), (-43876416461750 : ℤ)],
        ![(-269915285196125 : ℤ), (-210791415856125 : ℤ), (168598442860625 : ℤ), (87909569855875 : ℤ)],
        ![(-161128922761750 : ℤ), (168598442860625 : ℤ), (29644348912500 : ℤ), (-34159998645875 : ℤ)],
        ![(83725236724500 : ℤ), (12058405109125 : ℤ), (-9336083713125 : ℤ), (1267760404375 : ℤ)]],
      ![![(535041122672789 : ℤ), (-269915285196125 : ℤ), (-161128922761750 : ℤ), (83725236724500 : ℤ)],
        ![(-269915285196125 : ℤ), (-210791415856125 : ℤ), (168598442860625 : ℤ), (12058405109125 : ℤ)],
        ![(-161128922761750 : ℤ), (168598442860625 : ℤ), (29644348912500 : ℤ), (-9336083713125 : ℤ)],
        ![(83725236724500 : ℤ), (12058405109125 : ℤ), (-9336083713125 : ℤ), (-248374334125 : ℤ)]]],
    ![
      ![![(554611632595914 : ℤ), (-257086533024375 : ℤ), (-177902124838500 : ℤ), (-50390242502000 : ℤ)],
        ![(-257086533024375 : ℤ), (-228291690766875 : ℤ), (156058932228875 : ℤ), (92296178897750 : ℤ)],
        ![(-177902124838500 : ℤ), (156058932228875 : ℤ), (49144608648125 : ℤ), (-32429715972625 : ℤ)],
        ![(-50390242502000 : ℤ), (92296178897750 : ℤ), (-32429715972625 : ℤ), (-15939685537625 : ℤ)]],
      ![![(554611632595914 : ℤ), (-257086533024375 : ℤ), (-177902124838500 : ℤ), (85935673075000 : ℤ)],
        ![(-257086533024375 : ℤ), (-228291690766875 : ℤ), (156058932228875 : ℤ), (18479154672500 : ℤ)],
        ![(-177902124838500 : ℤ), (156058932228875 : ℤ), (49144608648125 : ℤ), (-12394806743625 : ℤ)],
        ![(-50390242502000 : ℤ), (92296178897750 : ℤ), (-32429715972625 : ℤ), (-56164008375 : ℤ)]],
      ![![(554611632595914 : ℤ), (-257086533024375 : ℤ), (-177902124838500 : ℤ), (-50390242502000 : ℤ)],
        ![(-257086533024375 : ℤ), (-228291690766875 : ℤ), (156058932228875 : ℤ), (92296178897750 : ℤ)],
        ![(-177902124838500 : ℤ), (156058932228875 : ℤ), (49144608648125 : ℤ), (-32429715972625 : ℤ)],
        ![(85935673075000 : ℤ), (18479154672500 : ℤ), (-12394806743625 : ℤ), (-56164008375 : ℤ)]],
      ![![(554611632595914 : ℤ), (-257086533024375 : ℤ), (-177902124838500 : ℤ), (85935673075000 : ℤ)],
        ![(-257086533024375 : ℤ), (-228291690766875 : ℤ), (156058932228875 : ℤ), (18479154672500 : ℤ)],
        ![(-177902124838500 : ℤ), (156058932228875 : ℤ), (49144608648125 : ℤ), (-12394806743625 : ℤ)],
        ![(85935673075000 : ℤ), (18479154672500 : ℤ), (-12394806743625 : ℤ), (4126224875 : ℤ)]]],
    ![
      ![![(573204736964664 : ℤ), (-249813598363250 : ℤ), (-185167346547750 : ℤ), (-49463527244875 : ℤ)],
        ![(-249813598363250 : ℤ), (-234507577937000 : ℤ), (142406802028750 : ℤ), (84716530456625 : ℤ)],
        ![(-185167346547750 : ℤ), (142406802028750 : ℤ), (57083820946750 : ℤ), (-26568431761750 : ℤ)],
        ![(-49463527244875 : ℤ), (84716530456625 : ℤ), (-26568431761750 : ℤ), (-5621222879750 : ℤ)]],
      ![![(573204736964664 : ℤ), (-249813598363250 : ℤ), (-185167346547750 : ℤ), (85716168300125 : ℤ)],
        ![(-249813598363250 : ℤ), (-234507577937000 : ℤ), (142406802028750 : ℤ), (22925673249125 : ℤ)],
        ![(-185167346547750 : ℤ), (142406802028750 : ℤ), (57083820946750 : ℤ), (-12674798180500 : ℤ)],
        ![(-49463527244875 : ℤ), (84716530456625 : ℤ), (-26568431761750 : ℤ), (-1162959186500 : ℤ)]],
      ![![(573204736964664 : ℤ), (-249813598363250 : ℤ), (-185167346547750 : ℤ), (-49463527244875 : ℤ)],
        ![(-249813598363250 : ℤ), (-234507577937000 : ℤ), (142406802028750 : ℤ), (84716530456625 : ℤ)],
        ![(-185167346547750 : ℤ), (142406802028750 : ℤ), (57083820946750 : ℤ), (-26568431761750 : ℤ)],
        ![(85716168300125 : ℤ), (22925673249125 : ℤ), (-12674798180500 : ℤ), (-1162959186500 : ℤ)]],
      ![![(573204736964664 : ℤ), (-249813598363250 : ℤ), (-185167346547750 : ℤ), (85716168300125 : ℤ)],
        ![(-249813598363250 : ℤ), (-234507577937000 : ℤ), (142406802028750 : ℤ), (22925673249125 : ℤ)],
        ![(-185167346547750 : ℤ), (142406802028750 : ℤ), (57083820946750 : ℤ), (-12674798180500 : ℤ)],
        ![(85716168300125 : ℤ), (22925673249125 : ℤ), (-12674798180500 : ℤ), (-227925870750 : ℤ)]]],
    ![
      ![![(588334024811289 : ℤ), (-226059002112875 : ℤ), (-202018753974625 : ℤ), (-57009146951375 : ℤ)],
        ![(-226059002112875 : ℤ), (-252421987203375 : ℤ), (115012240098250 : ℤ), (86123573974500 : ℤ)],
        ![(-202018753974625 : ℤ), (115012240098250 : ℤ), (82530985507250 : ℤ), (-21305045908000 : ℤ)],
        ![(-57009146951375 : ℤ), (86123573974500 : ℤ), (-21305045908000 : ℤ), (-13194193540375 : ℤ)]],
      ![![(588334024811289 : ℤ), (-226059002112875 : ℤ), (-202018753974625 : ℤ), (86194141490125 : ℤ)],
        ![(-226059002112875 : ℤ), (-252421987203375 : ℤ), (115012240098250 : ℤ), (34117590197250 : ℤ)],
        ![(-202018753974625 : ℤ), (115012240098250 : ℤ), (82530985507250 : ℤ), (-14220065455750 : ℤ)],
        ![(-57009146951375 : ℤ), (86123573974500 : ℤ), (-21305045908000 : ℤ), (-3207895486875 : ℤ)]],
      ![![(588334024811289 : ℤ), (-226059002112875 : ℤ), (-202018753974625 : ℤ), (-57009146951375 : ℤ)],
        ![(-226059002112875 : ℤ), (-252421987203375 : ℤ), (115012240098250 : ℤ), (86123573974500 : ℤ)],
        ![(-202018753974625 : ℤ), (115012240098250 : ℤ), (82530985507250 : ℤ), (-21305045908000 : ℤ)],
        ![(86194141490125 : ℤ), (34117590197250 : ℤ), (-14220065455750 : ℤ), (-3207895486875 : ℤ)]],
      ![![(588334024811289 : ℤ), (-226059002112875 : ℤ), (-202018753974625 : ℤ), (86194141490125 : ℤ)],
        ![(-226059002112875 : ℤ), (-252421987203375 : ℤ), (115012240098250 : ℤ), (34117590197250 : ℤ)],
        ![(-202018753974625 : ℤ), (115012240098250 : ℤ), (82530985507250 : ℤ), (-14220065455750 : ℤ)],
        ![(86194141490125 : ℤ), (34117590197250 : ℤ), (-14220065455750 : ℤ), (-758853840875 : ℤ)]]]]

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
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              (Certificate.splitX (-576 : ℤ)
                Certificate.inside
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  Certificate.inside)))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                Certificate.inside
                Certificate.inside)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-336 : ℤ)
                        Certificate.inside
                        Certificate.inside))
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        Certificate.inside)
                      Certificate.inside))
                  Certificate.inside)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-96 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-48 : ℤ)
                        (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                        (Certificate.splitY (-48 : ℤ)
                          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                          (Certificate.cross (-44781892370711 : ℤ) (109951162777600 : ℕ) none))))))))))),
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-1344 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-1440 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-1488 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.splitX (-1512 : ℤ)
                            (Certificate.splitY (216 : ℤ)
                              Certificate.inside
                              (Certificate.splitX (-1524 : ℤ)
                                (Certificate.splitY (228 : ℤ)
                                  Certificate.inside
                                  Certificate.inside)
                                Certificate.inside))
                            Certificate.inside)
                          Certificate.inside)
                        Certificate.inside)
                      Certificate.inside)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.inside
                      Certificate.inside)))
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  Certificate.inside))
              Certificate.inside)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-960 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                Certificate.inside)
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)))
          (Certificate.cross (-207977175769543 : ℤ) (879609302220800 : ℕ) none))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                Certificate.inside
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-480 : ℤ)
                    Certificate.inside
                    (Certificate.cross (-1741473521523877 : ℤ) (3518437208883200 : ℕ) none))))
              (Certificate.cross (-6838551112220251 : ℤ) (10555311626649600 : ℕ) none))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.cross (-272525319267029317 : ℤ) (900719925474099200 : ℕ) none)
                        (Certificate.splitY (144 : ℤ)
                          (Certificate.cross (-137128891131334567 : ℤ) (900719925474099200 : ℕ) none)
                          (Certificate.splitX (-216 : ℤ)
                            (Certificate.cross (-32362984964139753161 : ℤ) (61248954932238745600 : ℕ) none)
                            (Certificate.cross (-122772784069288003 : ℤ) (225179981368524800 : ℕ) none))))))
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-336 : ℤ)
                        (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.cross (-2262446900957277161 : ℤ) (7205759403792793600 : ℕ) none)
                          (Certificate.cross (-8661192807106503067 : ℤ) (14411518807585587200 : ℕ) none)))
                      (Certificate.cross (-26309891647351633 : ℤ) (40462027902156800 : ℕ) none))
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.splitX (-264 : ℤ)
                            (Certificate.cross (-2212788549843460508429 : ℤ) (3919933115663279718400 : ℕ) none)
                            (Certificate.cross (-535664300256525207163 : ℤ) (922337203685477580800 : ℕ) none))
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                        (Certificate.splitY (48 : ℤ)
                          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                          (Certificate.cross (-6667664295594078067 : ℤ) (14411518807585587200 : ℕ) none)))
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (144 : ℤ)
                          (Certificate.splitX (-168 : ℤ)
                            (Certificate.cross (-110430408818835040687 : ℤ) (230584300921369395200 : ℕ) none)
                            (Certificate.cross (-465212694005290389163 : ℤ) (922337203685477580800 : ℕ) none))
                          Certificate.outside)
                        Certificate.outside))
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.splitX (-48 : ℤ)
                        (Certificate.splitY (48 : ℤ)
                          (Certificate.cross (-392466870985977768163 : ℤ) (922337203685477580800 : ℕ) none)
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside))
                  Certificate.outside))
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (672 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (-336 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (720 : ℤ)
                          Certificate.outside
                          Certificate.outside)))
                    (Certificate.splitY (672 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (624 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (-216 : ℤ)
                            Certificate.outside
                            Certificate.outside)))
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (720 : ℤ)
                          (Certificate.splitX (-264 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (696 : ℤ)
                              Certificate.outside
                              Certificate.outside))
                          Certificate.outside)
                        (Certificate.splitY (720 : ℤ)
                          (Certificate.splitX (-216 : ℤ)
                            (Certificate.splitY (696 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            Certificate.outside)
                          Certificate.outside)))))
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      Certificate.outside))
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (672 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (624 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)
                    Certificate.outside)))))
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (1152 : ℤ)
              Certificate.outside
              (Certificate.splitX (-576 : ℤ)
                (Certificate.splitY (1344 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (-672 : ℤ)
                    (Certificate.splitY (1440 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (-720 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (1488 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (-696 : ℤ)
                            (Certificate.splitY (1512 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (-708 : ℤ)
                                Certificate.outside
                                Certificate.outside))
                            Certificate.outside))))
                    Certificate.outside))
                Certificate.outside))
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (960 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.outside
                    Certificate.outside)
                  Certificate.outside)
                Certificate.outside)
              Certificate.outside)))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                (Certificate.splitY (-1344 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-1440 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (-1488 : ℤ)
                          (Certificate.splitX (216 : ℤ)
                            Certificate.inside
                            (Certificate.splitY (-1512 : ℤ)
                              (Certificate.splitX (228 : ℤ)
                                Certificate.inside
                                Certificate.inside)
                              Certificate.inside))
                          Certificate.inside)
                        Certificate.inside)
                      Certificate.inside)
                    Certificate.inside)
                  Certificate.inside))
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                Certificate.inside))
            (Certificate.cross (0 : ℤ) (1 : ℕ) none))
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                (Certificate.splitY (-576 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (288 : ℤ)
                    Certificate.inside
                    (Certificate.cross (-1741473521523877 : ℤ) (3518437208883200 : ℕ) none))))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (144 : ℤ)
                        (Certificate.cross (-137128891131334567 : ℤ) (900719925474099200 : ℕ) none)
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.cross (-272525319267029317 : ℤ) (900719925474099200 : ℕ) none)
                          (Certificate.splitX (168 : ℤ)
                            (Certificate.cross (-30905308775803946411 : ℤ) (61248954932238745600 : ℕ) none)
                            (Certificate.cross (-122772784069288003 : ℤ) (225179981368524800 : ℕ) none))))))
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (48 : ℤ)
                        (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                          (Certificate.cross (-6667664295594078067 : ℤ) (14411518807585587200 : ℕ) none)))
                      (Certificate.splitX (48 : ℤ)
                        (Certificate.splitY (-48 : ℤ)
                          (Certificate.cross (-392466870985977768163 : ℤ) (922337203685477580800 : ℕ) none)
                          Certificate.outside)
                        Certificate.outside))
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (144 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (120 : ℤ)
                            (Certificate.cross (-1771969168154793263429 : ℤ) (3919933115663279718400 : ℕ) none)
                            (Certificate.cross (-465212694005290389163 : ℤ) (922337203685477580800 : ℕ) none))
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.cross (-2262446900957277161 : ℤ) (7205759403792793600 : ℕ) none)
                        (Certificate.splitY (-336 : ℤ)
                          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                          (Certificate.cross (-8661192807106503067 : ℤ) (14411518807585587200 : ℕ) none)))
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.splitX (216 : ℤ)
                            (Certificate.cross (-2152345767752903758679 : ℤ) (3919933115663279718400 : ℕ) none)
                            (Certificate.cross (-535664300256525207163 : ℤ) (922337203685477580800 : ℕ) none))
                          Certificate.outside)
                        Certificate.outside))
                    (Certificate.cross (-32877289304954133 : ℤ) (49258120924364800 : ℕ) none))
                  Certificate.outside)))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (-6838551112220251 : ℤ) (10555311626649600 : ℕ) none)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (480 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (672 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (624 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (648 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside)))))
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (720 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      (Certificate.splitX (720 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.splitX (696 : ℤ)
                            (Certificate.splitY (-264 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (-264 : ℤ)
                              Certificate.outside
                              Certificate.outside))
                          (Certificate.splitX (696 : ℤ)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            Certificate.outside))
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside))))
                  (Certificate.splitX (672 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (624 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      Certificate.outside)
                    Certificate.outside))))))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.cross (-207977175769543 : ℤ) (879609302220800 : ℕ) none)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              Certificate.outside
              (Certificate.splitX (960 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (864 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    Certificate.outside)
                  Certificate.outside)
                Certificate.outside))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (1344 : ℤ)
                Certificate.outside
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.splitX (1440 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (-672 : ℤ)
                      (Certificate.splitX (1488 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (-720 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1512 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (-696 : ℤ)
                              (Certificate.splitX (1524 : ℤ)
                                Certificate.outside
                                (Certificate.splitY (-708 : ℤ)
                                  Certificate.outside
                                  Certificate.outside))
                              Certificate.outside))))
                      Certificate.outside))
                  Certificate.outside))
              Certificate.outside)))),
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
                      (Certificate.splitX (144 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (336 : ℤ)
                          Certificate.outside
                          Certificate.outside)))))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (96 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (336 : ℤ)
                        Certificate.outside
                        Certificate.outside)))
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (216 : ℤ)
                            Certificate.outside
                            Certificate.outside))
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.splitX (264 : ℤ)
                            Certificate.outside
                            Certificate.outside)
                          Certificate.outside))
                      (Certificate.splitX (240 : ℤ)
                        Certificate.outside
                        Certificate.outside))
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside))))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    Certificate.outside
                    Certificate.outside)
                  Certificate.outside)
                Certificate.outside))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    Certificate.outside)
                  Certificate.outside)
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
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              (Certificate.splitX (-576 : ℤ)
                Certificate.inside
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  Certificate.inside)))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                Certificate.inside
                Certificate.inside)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-336 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.inside
                          Certificate.inside)))
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.inside
                        Certificate.inside)
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.inside
                          Certificate.inside)
                        Certificate.inside)))
                  Certificate.inside)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-96 : ℤ)
                    Certificate.inside
                    (Certificate.cross (-4904897071737 : ℤ) (27487790694400 : ℕ) none)))))))),
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-1344 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-1440 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-1488 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.splitX (-1512 : ℤ)
                            (Certificate.splitY (216 : ℤ)
                              Certificate.inside
                              (Certificate.splitX (-1524 : ℤ)
                                (Certificate.splitY (228 : ℤ)
                                  Certificate.inside
                                  (Certificate.splitX (-1530 : ℤ)
                                    (Certificate.splitY (234 : ℤ)
                                      Certificate.inside
                                      Certificate.inside)
                                    Certificate.inside))
                                Certificate.inside))
                            Certificate.inside)
                          Certificate.inside)
                        Certificate.inside)
                      Certificate.inside)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.inside
                      Certificate.inside)))
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  Certificate.inside))
              Certificate.inside)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-960 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                Certificate.inside)
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)))
          (Certificate.cross (0 : ℤ) (1 : ℕ) none))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.cross (-358526180042793 : ℤ) (1759218604441600 : ℕ) none)
              (Certificate.cross (-698897630964547 : ℤ) (1264438371942400 : ℕ) none))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (144 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-54843047949830877 : ℤ) (112589990684262400 : ℕ) none)))))
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-336 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-3896161747626872253 : ℤ) (7205759403792793600 : ℕ) none)))
                      (Certificate.cross (-33936819016886911 : ℤ) (56294995342131200 : ℕ) none))
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.splitX (-264 : ℤ)
                            (Certificate.cross (-694635522560655049411 : ℤ) (1383505805528216371200 : ℕ) none)
                            (Certificate.splitY (216 : ℤ)
                              (Certificate.cross (-667842654241381673161 : ℤ) (1383505805528216371200 : ℕ) none)
                              (Certificate.cross (-250256631703664572317 : ℤ) (461168601842738790400 : ℕ) none)))
                          (Certificate.cross (-75976868625241202899 : ℤ) (129703669268270284800 : ℕ) none))
                        (Certificate.cross (-1876090840932602891 : ℤ) (3152519739159347200 : ℕ) none))
                      Certificate.outside)))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.cross (-2173241802564449253 : ℤ) (7205759403792793600 : ℕ) none)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (144 : ℤ)
                          (Certificate.cross (-184300808839802686317 : ℤ) (461168601842738790400 : ℕ) none)
                          (Certificate.cross (-8341480751379902003 : ℤ) (16212958658533785600 : ℕ) none))
                        (Certificate.cross (-1667853421386216641 : ℤ) (3152519739159347200 : ℕ) none)))
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.cross (-5724863142260711 : ℤ) (12314530231091200 : ℕ) none)
                      Certificate.outside))
                  Certificate.outside))
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (672 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (624 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (-216 : ℤ)
                            Certificate.outside
                            Certificate.outside)))
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (720 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (-264 : ℤ)
                            Certificate.outside
                            Certificate.outside))
                        (Certificate.splitY (720 : ℤ)
                          (Certificate.splitX (-216 : ℤ)
                            (Certificate.splitY (696 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (696 : ℤ)
                              Certificate.outside
                              Certificate.outside))
                          Certificate.outside)))))
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      Certificate.outside))
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (672 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (624 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)
                    Certificate.outside)))))
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                Certificate.outside
                Certificate.outside)
              (Certificate.splitX (-576 : ℤ)
                (Certificate.splitY (1344 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (-672 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (1440 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (-624 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (1488 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (-600 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (1512 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (-588 : ℤ)
                                Certificate.outside
                                Certificate.outside))))))))
                Certificate.outside))
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (960 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (864 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (864 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      Certificate.outside))
                  Certificate.outside)
                Certificate.outside)
              Certificate.outside)))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                (Certificate.splitY (-1344 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-1440 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (-1488 : ℤ)
                          (Certificate.splitX (216 : ℤ)
                            Certificate.inside
                            (Certificate.splitY (-1512 : ℤ)
                              (Certificate.splitX (228 : ℤ)
                                Certificate.inside
                                (Certificate.splitY (-1524 : ℤ)
                                  (Certificate.splitX (234 : ℤ)
                                    Certificate.inside
                                    Certificate.inside)
                                  Certificate.inside))
                              Certificate.inside))
                          Certificate.inside)
                        Certificate.inside)
                      Certificate.inside)
                    Certificate.inside)
                  Certificate.inside))
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                Certificate.inside))
            (Certificate.cross (0 : ℤ) (1 : ℕ) none))
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (-358526180042793 : ℤ) (1759218604441600 : ℕ) none)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (144 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-54843047949830877 : ℤ) (112589990684262400 : ℕ) none)))))
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.cross (-2173241802564449253 : ℤ) (7205759403792793600 : ℕ) none)
                      (Certificate.cross (-5724863142260711 : ℤ) (12314530231091200 : ℕ) none))
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (144 : ℤ)
                        (Certificate.cross (-59924791336469134399 : ℤ) (129703669268270284800 : ℕ) none)
                        (Certificate.cross (-1667853421386216641 : ℤ) (3152519739159347200 : ℕ) none))
                      Certificate.outside)))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        Certificate.inside
                        (Certificate.cross (-3896161747626872253 : ℤ) (7205759403792793600 : ℕ) none))
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.splitX (216 : ℤ)
                            (Certificate.cross (-667842654241381673161 : ℤ) (1383505805528216371200 : ℕ) none)
                            (Certificate.cross (-250256631703664572317 : ℤ) (461168601842738790400 : ℕ) none))
                          (Certificate.cross (-9066652054888693253 : ℤ) (16212958658533785600 : ℕ) none))
                        (Certificate.cross (-1876090840932602891 : ℤ) (3152519739159347200 : ℕ) none)))
                    (Certificate.cross (-58232647948585891 : ℤ) (91479367430963200 : ℕ) none))
                  Certificate.outside)))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (-698897630964547 : ℤ) (1264438371942400 : ℕ) none)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (480 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (672 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (624 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (648 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside)))))
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (720 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (696 : ℤ)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside)))
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.splitX (744 : ℤ)
                            Certificate.outside
                            Certificate.outside)
                          Certificate.outside))))
                  (Certificate.splitX (672 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (624 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          Certificate.outside))
                      Certificate.outside)
                    Certificate.outside))))))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (960 : ℤ)
                Certificate.outside
                (Certificate.splitY (-576 : ℤ)
                  Certificate.outside
                  Certificate.outside))
              (Certificate.splitX (960 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (864 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (816 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside))
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      Certificate.outside))
                  Certificate.outside)
                Certificate.outside))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (1344 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                (Certificate.splitY (-576 : ℤ)
                  (Certificate.splitX (1440 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (-672 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1488 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (-624 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1512 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (-600 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (1524 : ℤ)
                                Certificate.outside
                                (Certificate.splitY (-588 : ℤ)
                                  Certificate.outside
                                  Certificate.outside))))))))
                  Certificate.outside))
              Certificate.outside)))),
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
                      (Certificate.splitX (144 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (336 : ℤ)
                          Certificate.outside
                          Certificate.outside)))))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (96 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (336 : ℤ)
                        Certificate.outside
                        Certificate.outside)))
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (216 : ℤ)
                            Certificate.outside
                            Certificate.outside))
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.splitX (264 : ℤ)
                            Certificate.outside
                            Certificate.outside)
                          (Certificate.splitX (264 : ℤ)
                            Certificate.outside
                            Certificate.outside)))
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside))
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside)
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
                    (Certificate.splitY (96 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    Certificate.outside)
                  Certificate.outside)
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
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              (Certificate.splitX (-576 : ℤ)
                Certificate.inside
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  Certificate.inside)))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                Certificate.inside
                Certificate.inside)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-336 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.splitX (-312 : ℤ)
                            Certificate.inside
                            (Certificate.splitY (-264 : ℤ)
                              Certificate.inside
                              Certificate.inside))
                          Certificate.inside)))
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-264 : ℤ)
                            Certificate.inside
                            Certificate.inside))
                        Certificate.inside)
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.splitX (-264 : ℤ)
                            (Certificate.splitY (-264 : ℤ)
                              Certificate.inside
                              Certificate.inside)
                            Certificate.inside)
                          Certificate.inside)
                        Certificate.inside)))
                  Certificate.inside)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  (Certificate.cross (0 : ℤ) (1 : ℕ) none))))))),
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-1344 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-1440 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-1488 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-1512 : ℤ)
                            (Certificate.splitY (264 : ℤ)
                              (Certificate.splitX (-1524 : ℤ)
                                (Certificate.splitY (252 : ℤ)
                                  Certificate.inside
                                  Certificate.inside)
                                Certificate.inside)
                              Certificate.inside)
                            Certificate.inside))
                        Certificate.inside)
                      Certificate.inside)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.inside
                      Certificate.inside)))
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  Certificate.inside))
              Certificate.inside)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-960 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                Certificate.inside)
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)))
          (Certificate.cross (0 : ℤ) (1 : ℕ) none))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)
              (Certificate.cross (-388452150912841 : ℤ) (879609302220800 : ℕ) none))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (144 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-98686864350636881 : ℤ) (225179981368524800 : ℕ) none)))))
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-336 : ℤ)
                        Certificate.inside
                        (Certificate.cross (-6534116888733518009 : ℤ) (14411518807585587200 : ℕ) none))
                      (Certificate.cross (-593271426677703881 : ℤ) (1069604911500492800 : ℕ) none))
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.splitX (-264 : ℤ)
                            (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                            (Certificate.splitY (216 : ℤ)
                              (Certificate.cross (-9833230795751901733 : ℤ) (461168601842738790400 : ℕ) none)
                              (Certificate.cross (-468882917109670628201 : ℤ) (922337203685477580800 : ℕ) none)))
                          (Certificate.cross (-185080763524581961447 : ℤ) (331464932574468505600 : ℕ) none))
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.cross (-22307020273336100009 : ℤ) (41433116571808563200 : ℕ) none)
                          Certificate.outside))
                      Certificate.outside)))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.cross (-1823634646252007009 : ℤ) (14411518807585587200 : ℕ) none)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (144 : ℤ)
                          (Certificate.cross (-272913028034676806201 : ℤ) (922337203685477580800 : ℕ) none)
                          (Certificate.cross (-20153857757341610759 : ℤ) (41433116571808563200 : ℕ) none))
                        (Certificate.cross (-4339745007584744173 : ℤ) (8556839292003942400 : ℕ) none)))
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.cross (-7170390622196879 : ℤ) (16712576742195200 : ℕ) none)
                      Certificate.outside))
                  Certificate.outside))
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (672 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (720 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (720 : ℤ)
                          (Certificate.splitX (-216 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (696 : ℤ)
                              Certificate.outside
                              Certificate.outside))
                          (Certificate.splitX (-216 : ℤ)
                            Certificate.outside
                            Certificate.outside))))))
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      Certificate.outside))
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (672 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (624 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (-168 : ℤ)
                            Certificate.outside
                            Certificate.outside))
                        (Certificate.splitY (624 : ℤ)
                          Certificate.outside
                          Certificate.outside))
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (720 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside))
                    Certificate.outside)))))
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                Certificate.outside
                Certificate.outside)
              (Certificate.splitX (-576 : ℤ)
                Certificate.outside
                (Certificate.splitY (1344 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (-480 : ℤ)
                    (Certificate.splitY (1440 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (-528 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (1488 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (-504 : ℤ)
                            Certificate.outside
                            Certificate.outside))))
                    Certificate.outside))))
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (960 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (864 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      Certificate.outside))
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.outside
                    Certificate.outside))
                Certificate.outside)
              Certificate.outside)))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                (Certificate.splitY (-1344 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-1440 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-1488 : ℤ)
                          (Certificate.splitX (264 : ℤ)
                            (Certificate.splitY (-1512 : ℤ)
                              (Certificate.splitX (252 : ℤ)
                                Certificate.inside
                                Certificate.inside)
                              Certificate.inside)
                            Certificate.inside)
                          Certificate.inside))
                      Certificate.inside)
                    Certificate.inside)
                  Certificate.inside))
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                Certificate.inside))
            (Certificate.cross (0 : ℤ) (1 : ℕ) none))
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (144 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-98686864350636881 : ℤ) (225179981368524800 : ℕ) none)))))
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.cross (-1823634646252007009 : ℤ) (14411518807585587200 : ℕ) none)
                      (Certificate.cross (-7170390622196879 : ℤ) (16712576742195200 : ℕ) none))
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (144 : ℤ)
                        (Certificate.cross (-138984029861699828947 : ℤ) (331464932574468505600 : ℕ) none)
                        (Certificate.cross (-4339745007584744173 : ℤ) (8556839292003942400 : ℕ) none))
                      Certificate.outside)))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        Certificate.inside
                        (Certificate.cross (-6534116888733518009 : ℤ) (14411518807585587200 : ℕ) none))
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.splitX (216 : ℤ)
                            (Certificate.cross (-9833230795751901733 : ℤ) (461168601842738790400 : ℕ) none)
                            (Certificate.cross (-468882917109670628201 : ℤ) (922337203685477580800 : ℕ) none))
                          (Certificate.cross (-22307020273336100009 : ℤ) (41433116571808563200 : ℕ) none))
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.cross (-185080763524581961447 : ℤ) (331464932574468505600 : ℕ) none)
                          Certificate.outside)))
                    (Certificate.cross (-147207625301918407 : ℤ) (239253730204057600 : ℕ) none))
                  Certificate.outside)))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (-388452150912841 : ℤ) (879609302220800 : ℕ) none)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (480 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (672 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (720 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (696 : ℤ)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside)))
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (744 : ℤ)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            Certificate.outside)))))
                  (Certificate.splitX (672 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (624 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (-144 : ℤ)
                          (Certificate.splitX (648 : ℤ)
                            Certificate.outside
                            Certificate.outside)
                          Certificate.outside))
                      Certificate.outside)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (720 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)))))))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (960 : ℤ)
                Certificate.outside
                (Certificate.splitY (-576 : ℤ)
                  Certificate.outside
                  Certificate.outside))
              (Certificate.splitX (960 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (864 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (816 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside))
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      Certificate.outside))
                  Certificate.outside)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (1056 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    Certificate.outside)
                  Certificate.outside)))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (1344 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (1440 : ℤ)
                    (Certificate.splitY (-480 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (-480 : ℤ)
                      (Certificate.splitX (1488 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (-528 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1512 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (-504 : ℤ)
                              Certificate.outside
                              Certificate.outside))))
                      Certificate.outside))))
              Certificate.outside)))),
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
                      (Certificate.splitX (144 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (336 : ℤ)
                          Certificate.outside
                          Certificate.outside)))))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (96 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (336 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (144 : ℤ)
                          Certificate.outside
                          Certificate.outside))))
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (264 : ℤ)
                            Certificate.outside
                            Certificate.outside)))
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside))
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside)
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
                    (Certificate.splitY (96 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    Certificate.outside)
                  Certificate.outside)
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
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              (Certificate.splitX (-576 : ℤ)
                Certificate.inside
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  Certificate.inside)))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                Certificate.inside
                Certificate.inside)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-336 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.splitX (-312 : ℤ)
                            Certificate.inside
                            (Certificate.splitY (-264 : ℤ)
                              Certificate.inside
                              Certificate.inside))
                          Certificate.inside)))
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (-336 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-264 : ℤ)
                            Certificate.inside
                            Certificate.inside))
                        Certificate.inside)
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.splitX (-264 : ℤ)
                            (Certificate.splitY (-264 : ℤ)
                              Certificate.inside
                              Certificate.inside)
                            Certificate.inside)
                          Certificate.inside)
                        Certificate.inside)))
                  Certificate.inside)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  (Certificate.cross (0 : ℤ) (1 : ℕ) none))))))),
      (Certificate.splitX (-768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-1152 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-1344 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-1440 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-1488 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-1512 : ℤ)
                            (Certificate.splitY (264 : ℤ)
                              Certificate.inside
                              Certificate.inside)
                            Certificate.inside))
                        Certificate.inside)
                      Certificate.inside)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.inside
                      Certificate.inside)))
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  Certificate.inside))
              Certificate.inside)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-960 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                Certificate.inside)
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)))
          (Certificate.cross (0 : ℤ) (1 : ℕ) none))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)
              (Certificate.cross (-1385561878706969 : ℤ) (3408486046105600 : ℕ) none))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      (Certificate.cross (-8619906367284689 : ℤ) (28147497671065600 : ℕ) none)))
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.cross (-627503267831466971 : ℤ) (1801439850948198400 : ℕ) none)
                      (Certificate.cross (-127729628034748439 : ℤ) (239253730204057600 : ℕ) none))
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.splitX (-264 : ℤ)
                            Certificate.inside
                            (Certificate.cross (-53475677800811762519 : ℤ) (115292150460684697600 : ℕ) none))
                          (Certificate.splitX (-264 : ℤ)
                            (Certificate.cross (-168725306390394433019 : ℤ) (331464932574468505600 : ℕ) none)
                            (Certificate.cross (-37192938500090681893 : ℤ) (68454714336031539200 : ℕ) none)))
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.splitX (-216 : ℤ)
                            (Certificate.cross (-1342901548310931760027 : ℤ) (2651719460595748044800 : ℕ) none)
                            (Certificate.cross (-4440370863245697971 : ℤ) (8556839292003942400 : ℕ) none))
                          Certificate.outside))
                      Certificate.outside)))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.cross (-3869003792613807971 : ℤ) (8556839292003942400 : ℕ) none)
                        (Certificate.cross (-926689794525083137 : ℤ) (1914029841632460800 : ℕ) none)))
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.cross (-46976074677826657 : ℤ) (119626865102028800 : ℕ) none)
                      Certificate.outside))
                  Certificate.outside))
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (672 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (720 : ℤ)
                          (Certificate.splitX (-216 : ℤ)
                            Certificate.outside
                            Certificate.outside)
                          (Certificate.splitX (-216 : ℤ)
                            (Certificate.splitY (744 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            Certificate.outside))))))
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      Certificate.outside))
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (672 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (720 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside))
                    Certificate.outside)))))
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (-576 : ℤ)
                Certificate.outside
                Certificate.outside)
              (Certificate.splitX (-576 : ℤ)
                Certificate.outside
                (Certificate.splitY (1344 : ℤ)
                  (Certificate.splitX (-480 : ℤ)
                    Certificate.outside
                    Certificate.outside)
                  (Certificate.splitX (-480 : ℤ)
                    (Certificate.splitY (1440 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (-528 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (1488 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (-504 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (1512 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (-492 : ℤ)
                                Certificate.outside
                                Certificate.outside))))))
                    Certificate.outside))))
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (960 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (864 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (864 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (816 : ℤ)
                          (Certificate.splitX (-264 : ℤ)
                            Certificate.outside
                            Certificate.outside)
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside))
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.outside
                    Certificate.outside))
                Certificate.outside)
              Certificate.outside)))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                (Certificate.splitY (-1344 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-1440 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-1488 : ℤ)
                          (Certificate.splitX (264 : ℤ)
                            Certificate.inside
                            Certificate.inside)
                          Certificate.inside))
                      Certificate.inside)
                    Certificate.inside)
                  Certificate.inside))
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                Certificate.inside))
            (Certificate.cross (0 : ℤ) (1 : ℕ) none))
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (0 : ℤ) (1 : ℕ) none)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    Certificate.inside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.cross (-8619906367284689 : ℤ) (28147497671065600 : ℕ) none)))
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.cross (0 : ℤ) (1 : ℕ) none)
                      (Certificate.cross (-46976074677826657 : ℤ) (119626865102028800 : ℕ) none))
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (144 : ℤ)
                        (Certificate.cross (-25001367286045256893 : ℤ) (68454714336031539200 : ℕ) none)
                        (Certificate.cross (-926689794525083137 : ℤ) (1914029841632460800 : ℕ) none))
                      Certificate.outside)))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.cross (-627503267831466971 : ℤ) (1801439850948198400 : ℕ) none)
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.splitX (216 : ℤ)
                            Certificate.inside
                            (Certificate.cross (-53475677800811762519 : ℤ) (115292150460684697600 : ℕ) none))
                          (Certificate.splitX (216 : ℤ)
                            (Certificate.cross (-19544183615567120143 : ℤ) (41433116571808563200 : ℕ) none)
                            (Certificate.cross (-4440370863245697971 : ℤ) (8556839292003942400 : ℕ) none)))
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.splitX (264 : ℤ)
                            (Certificate.cross (-1380655020261605563777 : ℤ) (2651719460595748044800 : ℕ) none)
                            (Certificate.cross (-37192938500090681893 : ℤ) (68454714336031539200 : ℕ) none))
                          Certificate.outside)))
                    (Certificate.cross (-34233656558947633 : ℤ) (56294995342131200 : ℕ) none))
                  Certificate.outside)))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (-1385561878706969 : ℤ) (3408486046105600 : ℕ) none)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (480 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (672 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (720 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (696 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside)))
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (744 : ℤ)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside))))))
                  (Certificate.splitX (672 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (624 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          Certificate.outside))
                      Certificate.outside)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (720 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside)))))))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (960 : ℤ)
                Certificate.outside
                (Certificate.splitY (-576 : ℤ)
                  Certificate.outside
                  Certificate.outside))
              (Certificate.splitX (960 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (864 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (816 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.splitX (792 : ℤ)
                            (Certificate.splitY (-264 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (-264 : ℤ)
                              Certificate.outside
                              Certificate.outside))
                          Certificate.outside)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside)))
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      Certificate.outside))
                  Certificate.outside)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (1056 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    Certificate.outside)
                  Certificate.outside)))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (1344 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (1248 : ℤ)
                    (Certificate.splitY (-480 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (-480 : ℤ)
                      Certificate.outside
                      Certificate.outside)))
                (Certificate.splitY (-576 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (1440 : ℤ)
                    (Certificate.splitY (-480 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (-480 : ℤ)
                      (Certificate.splitX (1488 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (-528 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1512 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (-504 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (1524 : ℤ)
                                Certificate.outside
                                (Certificate.splitY (-492 : ℤ)
                                  Certificate.outside
                                  Certificate.outside))))))
                      Certificate.outside))))
              Certificate.outside)))),
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
                      (Certificate.splitX (144 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (336 : ℤ)
                          Certificate.outside
                          Certificate.outside)))))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (96 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (336 : ℤ)
                        Certificate.outside
                        Certificate.outside)))
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (264 : ℤ)
                            Certificate.outside
                            Certificate.outside)))
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside))
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside))))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      Certificate.outside))
                  Certificate.outside)
                Certificate.outside))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    Certificate.outside)
                  Certificate.outside)
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
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              (Certificate.splitX (-576 : ℤ)
                Certificate.inside
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  Certificate.inside)))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                Certificate.inside
                Certificate.inside)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-336 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.inside
                          Certificate.inside)))
                    (Certificate.splitY (-288 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.inside
                        Certificate.inside)
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.splitX (-264 : ℤ)
                            Certificate.inside
                            Certificate.inside)
                          Certificate.inside)
                        Certificate.inside)))
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.inside
                    Certificate.inside))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      Certificate.inside)
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
                      (Certificate.splitX (-1488 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (-1512 : ℤ)
                            (Certificate.splitY (264 : ℤ)
                              (Certificate.splitX (-1524 : ℤ)
                                (Certificate.splitY (252 : ℤ)
                                  (Certificate.splitX (-1530 : ℤ)
                                    (Certificate.splitY (246 : ℤ)
                                      Certificate.inside
                                      Certificate.inside)
                                    Certificate.inside)
                                  Certificate.inside)
                                Certificate.inside)
                              Certificate.inside)
                            Certificate.inside))
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          Certificate.inside))
                      Certificate.inside)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.inside
                      Certificate.inside)))
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-1248 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.inside
                      Certificate.inside)
                    Certificate.inside)))
              Certificate.inside)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-960 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  Certificate.inside)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  Certificate.inside))
              Certificate.inside))
          (Certificate.cross (0 : ℤ) (1 : ℕ) none))
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              Certificate.inside
              (Certificate.cross (-803708500850969 : ℤ) (3298534883328000 : ℕ) none))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      Certificate.inside
                      (Certificate.cross (-355078945204072631 : ℤ) (844424930131968000 : ℕ) none))
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.inside
                          (Certificate.cross (-103276840010980208947 : ℤ) (216172782113783808000 : ℕ) none))
                        (Certificate.splitY (240 : ℤ)
                          (Certificate.splitX (-216 : ℤ)
                            (Certificate.splitY (216 : ℤ)
                              Certificate.inside
                              (Certificate.cross (-3176716242664504271233 : ℤ) (6917529027641081856000 : ℕ) none))
                            (Certificate.cross (-12982810098634841009 : ℤ) (27021597764222976000 : ℕ) none))
                          (Certificate.cross (-3564580147311916423 : ℤ) (6755399441055744000 : ℕ) none)))
                      (Certificate.cross (-120763841155392157 : ℤ) (211106232532992000 : ℕ) none))))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.cross (-10980941999803235759 : ℤ) (27021597764222976000 : ℕ) none)
                        (Certificate.cross (-3028454115657992173 : ℤ) (6755399441055744000 : ℕ) none)))
                    (Certificate.splitY (96 : ℤ)
                      (Certificate.cross (-35869392878887657 : ℤ) (105553116266496000 : ℕ) none)
                      (Certificate.cross (-13327259925180629 : ℤ) (26388279066624000 : ℕ) none)))
                  (Certificate.cross (-21022443057416629 : ℤ) (35184372088832000 : ℕ) none)))
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.cross (-830204918653148253 : ℤ) (1407374883553280000 : ℕ) none)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (672 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (720 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (-216 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (744 : ℤ)
                              Certificate.outside
                              Certificate.outside)))))))
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (-96 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      Certificate.outside))
                  (Certificate.splitX (-96 : ℤ)
                    (Certificate.splitY (672 : ℤ)
                      (Certificate.splitX (-144 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      (Certificate.splitX (-144 : ℤ)
                        (Certificate.splitY (720 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside))
                    (Certificate.splitY (672 : ℤ)
                      Certificate.outside
                      Certificate.outside))))))
          (Certificate.splitX (-384 : ℤ)
            (Certificate.splitY (1152 : ℤ)
              (Certificate.cross (-12869147935749377 : ℤ) (43980465111040000 : ℕ) none)
              (Certificate.splitX (-576 : ℤ)
                Certificate.outside
                (Certificate.splitY (1344 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (-480 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (1440 : ℤ)
                      (Certificate.splitX (-432 : ℤ)
                        Certificate.outside
                        Certificate.outside)
                      (Certificate.splitX (-432 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (1488 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (-408 : ℤ)
                            (Certificate.splitY (1512 : ℤ)
                              Certificate.outside
                              (Certificate.splitX (-420 : ℤ)
                                Certificate.outside
                                Certificate.outside))
                            Certificate.outside))))))))
            (Certificate.splitY (1152 : ℤ)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (960 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (864 : ℤ)
                      (Certificate.splitX (-240 : ℤ)
                        (Certificate.splitY (816 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (816 : ℤ)
                          (Certificate.splitX (-216 : ℤ)
                            Certificate.outside
                            Certificate.outside)
                          Certificate.outside))
                      (Certificate.splitX (-240 : ℤ)
                        Certificate.outside
                        Certificate.outside)))
                  (Certificate.splitX (-288 : ℤ)
                    (Certificate.splitY (1056 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    Certificate.outside))
                Certificate.outside)
              (Certificate.splitX (-192 : ℤ)
                (Certificate.splitY (1344 : ℤ)
                  (Certificate.splitX (-288 : ℤ)
                    Certificate.outside
                    Certificate.outside)
                  Certificate.outside)
                Certificate.outside))))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (-768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-1152 : ℤ)
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                (Certificate.splitY (-1344 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-1440 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        Certificate.inside
                        (Certificate.splitY (-1488 : ℤ)
                          (Certificate.splitX (264 : ℤ)
                            (Certificate.splitY (-1512 : ℤ)
                              (Certificate.splitX (252 : ℤ)
                                (Certificate.splitY (-1524 : ℤ)
                                  (Certificate.splitX (246 : ℤ)
                                    Certificate.inside
                                    Certificate.inside)
                                  Certificate.inside)
                                Certificate.inside)
                              Certificate.inside)
                            Certificate.inside)
                          Certificate.inside))
                      Certificate.inside)
                    Certificate.inside)
                  (Certificate.splitX (288 : ℤ)
                    Certificate.inside
                    Certificate.inside)))
              (Certificate.splitX (192 : ℤ)
                Certificate.inside
                Certificate.inside))
            Certificate.inside)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              Certificate.inside
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  Certificate.inside
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.inside
                      (Certificate.cross (-35869392878887657 : ℤ) (105553116266496000 : ℕ) none))
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (144 : ℤ)
                        (Certificate.cross (-63382516952370256447 : ℤ) (216172782113783808000 : ℕ) none)
                        (Certificate.cross (-3028454115657992173 : ℤ) (6755399441055744000 : ℕ) none))
                      (Certificate.cross (-13327259925180629 : ℤ) (26388279066624000 : ℕ) none))))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.inside
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.inside
                          (Certificate.splitX (216 : ℤ)
                            (Certificate.cross (-45932058170492339197 : ℤ) (108086391056891904000 : ℕ) none)
                            (Certificate.splitY (-216 : ℤ)
                              (Certificate.cross (-3176716242664504271233 : ℤ) (6917529027641081856000 : ℕ) none)
                              (Certificate.cross (-12982810098634841009 : ℤ) (27021597764222976000 : ℕ) none))))
                        (Certificate.splitY (-240 : ℤ)
                          (Certificate.cross (-103276840010980208947 : ℤ) (216172782113783808000 : ℕ) none)
                          (Certificate.cross (-3564580147311916423 : ℤ) (6755399441055744000 : ℕ) none))))
                    (Certificate.cross (-120763841155392157 : ℤ) (211106232532992000 : ℕ) none))
                  (Certificate.cross (-21022443057416629 : ℤ) (35184372088832000 : ℕ) none))))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (-803708500850969 : ℤ) (3298534883328000 : ℕ) none)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.cross (-830204918653148253 : ℤ) (1407374883553280000 : ℕ) none)
                  (Certificate.splitX (480 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (-96 : ℤ)
                      Certificate.outside
                      Certificate.outside)))
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (672 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (720 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (744 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside))))))
                  (Certificate.splitX (672 : ℤ)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (624 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          Certificate.outside))
                      Certificate.outside)
                    (Certificate.splitY (-96 : ℤ)
                      (Certificate.splitX (720 : ℤ)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (-144 : ℤ)
                          Certificate.outside
                          Certificate.outside))
                      Certificate.outside)))))))
        (Certificate.splitY (-768 : ℤ)
          (Certificate.cross (0 : ℤ) (1 : ℕ) none)
          (Certificate.splitX (1152 : ℤ)
            (Certificate.splitY (-384 : ℤ)
              (Certificate.cross (-12869147935749377 : ℤ) (43980465111040000 : ℕ) none)
              (Certificate.splitX (960 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (864 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (816 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (792 : ℤ)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside)
                            (Certificate.splitY (-216 : ℤ)
                              Certificate.outside
                              Certificate.outside)))
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside)))
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (912 : ℤ)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (-240 : ℤ)
                          Certificate.outside
                          Certificate.outside))))
                  Certificate.outside)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (1056 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      Certificate.outside))
                  Certificate.outside)))
            (Certificate.splitY (-384 : ℤ)
              (Certificate.splitX (1344 : ℤ)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.outside
                  Certificate.outside)
                (Certificate.splitY (-576 : ℤ)
                  Certificate.outside
                  (Certificate.splitX (1440 : ℤ)
                    (Certificate.splitY (-480 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1392 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (-432 : ℤ)
                          Certificate.outside
                          Certificate.outside)))
                    (Certificate.splitY (-480 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (1488 : ℤ)
                        (Certificate.splitY (-432 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        (Certificate.splitY (-432 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (1512 : ℤ)
                            Certificate.outside
                            (Certificate.splitY (-408 : ℤ)
                              (Certificate.splitX (1524 : ℤ)
                                Certificate.outside
                                (Certificate.splitY (-420 : ℤ)
                                  Certificate.outside
                                  Certificate.outside))
                              Certificate.outside))))))))
              (Certificate.splitX (1344 : ℤ)
                (Certificate.splitY (-192 : ℤ)
                  (Certificate.splitX (1248 : ℤ)
                    (Certificate.splitY (-288 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    Certificate.outside)
                  Certificate.outside)
                Certificate.outside))))),
      (Certificate.splitX (768 : ℤ)
        (Certificate.splitY (768 : ℤ)
          (Certificate.splitX (384 : ℤ)
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.cross (-199939901697994407 : ℤ) (351843720888320000 : ℕ) none)
                  (Certificate.splitX (96 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (288 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (144 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (336 : ℤ)
                          Certificate.outside
                          Certificate.outside)))))
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (288 : ℤ)
                    Certificate.outside
                    (Certificate.splitY (96 : ℤ)
                      Certificate.outside
                      (Certificate.splitX (336 : ℤ)
                        Certificate.outside
                        Certificate.outside)))
                  (Certificate.splitX (288 : ℤ)
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (240 : ℤ)
                        Certificate.outside
                        (Certificate.splitY (240 : ℤ)
                          Certificate.outside
                          (Certificate.splitX (264 : ℤ)
                            Certificate.outside
                            Certificate.outside)))
                      (Certificate.splitX (240 : ℤ)
                        (Certificate.splitY (336 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside))
                    (Certificate.splitY (288 : ℤ)
                      (Certificate.splitX (336 : ℤ)
                        (Certificate.splitY (240 : ℤ)
                          Certificate.outside
                          Certificate.outside)
                        Certificate.outside)
                      Certificate.outside))))
              (Certificate.splitX (192 : ℤ)
                (Certificate.splitY (576 : ℤ)
                  (Certificate.splitX (96 : ℤ)
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    (Certificate.splitY (480 : ℤ)
                      Certificate.outside
                      Certificate.outside))
                  Certificate.outside)
                Certificate.outside))
            (Certificate.splitY (384 : ℤ)
              (Certificate.splitX (576 : ℤ)
                (Certificate.splitY (192 : ℤ)
                  (Certificate.splitX (480 : ℤ)
                    (Certificate.splitY (96 : ℤ)
                      Certificate.outside
                      Certificate.outside)
                    Certificate.outside)
                  Certificate.outside)
                Certificate.outside)
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

end BerryEsseen.N2NeededIntegerPointwise08

#print axioms BerryEsseen.N2NeededIntegerPointwise08.powers_entries
#print axioms BerryEsseen.N2NeededIntegerPointwise08.powers_eq
#print axioms BerryEsseen.N2NeededIntegerPointwise08.checks
#print axioms BerryEsseen.N2NeededIntegerPointwise08.pointwise
