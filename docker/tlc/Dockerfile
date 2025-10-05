FROM eclipse-temurin:17-jre

WORKDIR /opt

# Install TLA+ Toolbox
RUN apt-get update && \
    apt-get install -y wget && \
    wget https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar && \
    apt-get clean && \
    rm -rf /var/lib/apt/lists/*

# Create workspace directory
WORKDIR /workspace

# Default to idle so ad-hoc runs can override
ENTRYPOINT []
CMD ["sleep", "infinity"]
