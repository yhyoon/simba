dune build
dune install --prefix=_install
ln -s _install/bin/simba simba.exe
cp _install/bin/simba simba.`git rev-parse --short HEAD`.exe
