import Collatz.MCycle110Certs75

/-!
# Certificates of the listed shapes of `data110`, chunks 300..303
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_300 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_300 = true := by
  decide +kernel

theorem certs110_301 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_301 = true := by
  decide +kernel

theorem certs110_302 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_302 = true := by
  decide +kernel

theorem certs110_303 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_303 = true := by
  decide +kernel

end Collatz
