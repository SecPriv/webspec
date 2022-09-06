FROM webplatformtests/wpt:0.52 as base
ENV PIP_DISABLE_PIP_VERSION_CHECK=1
RUN sed -i 's/depth=50/depth=1/' start.sh
RUN ./start.sh https://github.com/webspec-framework/wpt.git master
WORKDIR web-platform-tests
RUN ./wpt run --help >/dev/null
RUN ./wpt install --channel stable chromium browser && ./wpt install --channel stable chromium webdriver
RUN ./wpt install --channel stable firefox browser && ./wpt install --channel stable firefox webdriver
RUN sed -i 's#cert_path = "../tools/certs/cacert.pem"#cert_path = "/home/test/web-platform-tests/tools/certs/cacert.pem"#' verifier/server.py
RUN sed -i 's#cert_path = "../tools/certs/cacert.pem"#cert_path = "/home/test/web-platform-tests/tools/certs/cacert.pem"#' verifier/csp.py

# TEST SPECIFIC
FROM base as test
RUN rm -f /home/test/web-platform-tests/verifier/responses/*
COPY output/config.json /home/test/web-platform-tests/
COPY output/launcher.html output/*_sw.js /home/test/web-platform-tests/verifier/
COPY output/*.body output/*.headers output/*.ver output/*_sw.html /home/test/web-platform-tests/verifier/responses/

FROM test as chromium
ENV CHROMIUM_BINARY=/home/test/web-platform-tests/_venv3/browsers/stable/chrome-linux/chrome
# ENTRYPOINT
CMD ./wpt make-hosts-file | grep 127.0.0.1 | sudo tee -a /etc/hosts >/dev/null; \
    ./wpt regen-certs --force ; \
    fnm=`find tools/certs -exec bash -c 'basename "$0" ".${0##*.}"' {} \; | sort | uniq --repeated | grep .test | grep -v web-platform` ; \
    mv "tools/certs/$fnm".key tools/certs/web-platform.test.key ; mv "tools/certs/$fnm".pem tools/certs/web-platform.test.pem  ; \
    xvfb-run ./wpt run --yes \
        --log-mach-level=warning \
        --log-mach=- \
        --log-wptreport=/dev/stderr \
        --channel stable \
        --binary $CHROMIUM_BINARY \
        --binary-arg no-gpu \
        --binary-arg no-sandbox \
        --binary-arg allow-running-insecure-content \
        --binary-arg ignore-certificate-errors \
        --no-pause-after-test \
        chromium \
        verifier/launcher.html

from test as firefox
ENV FIREFOX_BINARY=/home/test/web-platform-tests/_venv3/browsers/stable/firefox/firefox
# ENTRYPOINTA
USER root
RUN chown -R test /home/test/web-platform-tests/verifier
USER test 
CMD ./wpt make-hosts-file | grep 127.0.0.1 | sudo tee -a /etc/hosts >/dev/null; \
    ./wpt regen-certs --force; \
    fnm=`find tools/certs -exec bash -c 'basename "$0" ".${0##*.}"' {} \; | sort | uniq --repeated | grep .test | grep -v web-platform` ; \
    mv "tools/certs/$fnm".key tools/certs/web-platform.test.key ; mv "tools/certs/$fnm".pem tools/certs/web-platform.test.pem  ; \
    ./wpt run --yes \
        --log-mach-level=warning \
        --log-mach=- \
        --log-wptreport=/dev/stderr \
        --channel stable \
        --binary $FIREFOX_BINARY \
        --headless \
        --no-pause-after-test \
        firefox \
        verifier/launcher.html

