# time4block
Cardano block &lt;-> time calculator



## compilation

install 'Haste':

      $ nix-shell -p "haskellPackages.ghcWithPackages (self: with self; [haste-cabal-install haste-compiler])"


update its package:

      $ haste-cabal update


prepare Haste environment:

      $ haste-boot


