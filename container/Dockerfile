FROM amazoncorretto:17

RUN yum install -y \
  texlive-base \
  texlive-texconfig \
  texlive-texconfig-bin \
  texlive-collection-fontsrecommended \
  texlive-pdftex \
  texlive-latex-bin

ARG UID
ARG GID

RUN groupadd -g $GID tlausers && \
    useradd -u $UID -g tlausers tlauser

RUN mkdir /home/tlauser/tla/
RUN curl -L https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar -o /home/tlauser/tla/tla2tools.jar

ENV COMMUNITY_VER=202208261745
RUN curl -L https://github.com/tlaplus/CommunityModules/releases/download/${COMMUNITY_VER}/CommunityModules-${COMMUNITY_VER}.jar -o /home/tlauser/tla/CommunityModules.jar
RUN curl -L https://github.com/tlaplus/CommunityModules/releases/download/${COMMUNITY_VER}/CommunityModules-deps-${COMMUNITY_VER}.jar -o /home/tlauser/tla/CommunityModules-deps.jar

COPY home/tlauser/tla/*.* /home/tlauser/tla/
COPY home/tlauser/.bashrc /home/tlauser/.bashrc

RUN chown -R tlauser:tlausers /home/tlauser

USER tlauser

VOLUME /home/tlauser/src
WORKDIR /home/tlauser/src

ENTRYPOINT /bin/bash
