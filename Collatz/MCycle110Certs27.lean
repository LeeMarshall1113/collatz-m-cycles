import Collatz.MCycle110Certs26

/-!
# Certificates of the listed shapes of `data110`, chunks 104..107
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_104 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_104 = true := by
  decide +kernel

theorem certs110_105 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_105 = true := by
  decide +kernel

theorem certs110_106 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_106 = true := by
  decide +kernel

theorem certs110_107 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_107 = true := by
  decide +kernel

end Collatz
