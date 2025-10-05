type LogLevel = 'info' | 'warn' | 'error' | 'debug';

type NodeTools = {
  fs: typeof import('fs/promises');
  path: typeof import('path');
};

let nodeToolsPromise: Promise<NodeTools | null> | null = null;
let logFilePath: string | null = null;

function isEdgeRuntime(): boolean {
  return typeof process !== 'undefined' && process.env?.NEXT_RUNTIME === 'edge';
}

function canUseNodeApis(): boolean {
  return typeof process !== 'undefined' && !isEdgeRuntime() && !!process.cwd;
}

async function loadNodeTools(): Promise<NodeTools | null> {
  if (!canUseNodeApis()) {
    return null;
  }

  if (!nodeToolsPromise) {
    nodeToolsPromise = (async () => {
      try {
        const [fsModule, pathModule] = await Promise.all([
          import('fs/promises'),
          import('path'),
        ]);
        const path = (pathModule as any).default ?? pathModule;
        return { fs: fsModule, path } as NodeTools;
      } catch (error) {
        console.error('[Logger] Failed to load fs/path modules', error);
        return null;
      }
    })();
  }

  return nodeToolsPromise;
}

async function ensureLogFile(): Promise<{ file: string; tools: NodeTools } | null> {
  const tools = await loadNodeTools();
  if (!tools) {
    return null;
  }

  if (!logFilePath) {
    const baseDir = process.env.LOG_DIR ?? tools.path.join(process.cwd(), 'logs');
    const filePath = tools.path.join(baseDir, 'app.log');
    try {
      await tools.fs.mkdir(baseDir, { recursive: true });
      await tools.fs.appendFile(filePath, '');
      logFilePath = filePath;
    } catch (error) {
      console.error('[Logger] Failed to initialise log file', error);
      return null;
    }
  }

  return { file: logFilePath, tools };
}

class Logger {
  private log(level: LogLevel, message: string, meta?: any) {
    const timestamp = new Date().toISOString();
    const logMessage = `[${timestamp}] [${level.toUpperCase()}] ${message}`;

    if (meta) {
      console[level](logMessage, meta);
    } else {
      console[level](logMessage);
    }

    void this.writeToFile(`${logMessage}${meta ? ' ' + JSON.stringify(meta) : ''}`);
  }

  private async writeToFile(entry: string): Promise<void> {
    try {
      const fileContext = await ensureLogFile();
      if (!fileContext) {
        return;
      }

      const { tools, file } = fileContext;
      await tools.fs.appendFile(file, `${entry}\n`, 'utf-8');
    } catch (error) {
      // Swallow file logging errors to avoid impacting runtime behaviour
      console.error('[Logger] Failed to write log entry', error);
    }
  }

  info(message: string, meta?: any) {
    this.log('info', message, meta);
  }

  warn(message: string, meta?: any) {
    this.log('warn', message, meta);
  }

  error(message: string, meta?: any) {
    this.log('error', message, meta);
  }

  debug(message: string, meta?: any) {
    if (process.env.NODE_ENV === 'development') {
      this.log('debug', message, meta);
    }
  }
}

export const logger = new Logger();
