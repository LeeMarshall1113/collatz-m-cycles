import Collatz.MCycle110Certs20

/-!
# Certificates of the listed shapes of `data110`, chunks 80..83
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_80 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_80 = true := by
  decide +kernel

theorem certs110_81 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_81 = true := by
  decide +kernel

theorem certs110_82 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_82 = true := by
  decide +kernel

theorem certs110_83 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_83 = true := by
  decide +kernel

end Collatz
