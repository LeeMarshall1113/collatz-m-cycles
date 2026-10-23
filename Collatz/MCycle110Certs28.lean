import Collatz.MCycle110Certs27

/-!
# Certificates of the listed shapes of `data110`, chunks 108..111
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_108 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_108 = true := by
  decide +kernel

theorem certs110_109 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_109 = true := by
  decide +kernel

theorem certs110_110 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_110 = true := by
  decide +kernel

theorem certs110_111 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_111 = true := by
  decide +kernel

end Collatz
