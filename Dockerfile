FROM nixos/nix
ENV NIXPKGS_ALLOW_UNFREE 1
COPY shell.nix /opt/
ADD nix/ /opt/nix/
RUN nix-env -if /opt/shell.nix -A buildInputs --cores 9 -j 9
RUN nix-shell /opt/shell.nix
RUN nix-env -iA nixpkgs.emacs-nox
WORKDIR /mnt
RUN chmod -R 777 /nix/var/
RUN echo -e '#!/bin/sh\nnix-shell /opt/shell.nix --run "$(echo "$@")"' > /bin/entrypoint
RUN chmod +x /bin/entrypoint
ENTRYPOINT ["/bin/entrypoint"]
