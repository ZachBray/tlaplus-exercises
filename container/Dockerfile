FROM amazoncorretto:17

RUN yum install -y \
  texlive-base \
  texlive-texconfig \
  texlive-texconfig-bin \
  texlive-collection-fontsrecommended \
  texlive-pdftex \
  texlive-latex-bin

RUN mkdir /root/tla/
RUN curl -L https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar -o /root/tla/tla2tools.jar

ENV COMMUNITY_VER=202208261745
RUN curl -L https://github.com/tlaplus/CommunityModules/releases/download/${COMMUNITY_VER}/CommunityModules-${COMMUNITY_VER}.jar -o /root/tla/CommunityModules.jar
RUN curl -L https://github.com/tlaplus/CommunityModules/releases/download/${COMMUNITY_VER}/CommunityModules-deps-${COMMUNITY_VER}.jar -o /root/tla/CommunityModules-deps.jar

COPY root/tla/*.* /root/tla/
COPY root/.bashrc /root/.bashrc
VOLUME /root/src
WORKDIR /root/src

ENTRYPOINT /bin/bash
