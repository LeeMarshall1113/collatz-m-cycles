import Collatz.MCycle110Certs52

/-!
# Certificates of the listed shapes of `data110`, chunks 208..211
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_208 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_208 = true := by
  decide +kernel

theorem certs110_209 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_209 = true := by
  decide +kernel

theorem certs110_210 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_210 = true := by
  decide +kernel

theorem certs110_211 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_211 = true := by
  decide +kernel

end Collatz
