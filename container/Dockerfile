FROM amazoncorretto:17
RUN curl -L https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar -o /root/tla2tools.jar
COPY root/*.* /root/
VOLUME /root/src
WORKDIR /root/src
ENTRYPOINT /bin/bash
