import { MongoClient, Db } from 'mongodb';

type MongoConnection = {
  client: MongoClient;
  db: Db;
};

declare global {
  // eslint-disable-next-line no-var
  var __mongoConnection: MongoConnection | undefined;
}

const uri = process.env.MONGODB_URI;
const dbName = process.env.MONGODB_DB_NAME ?? 'guardrails';

if (!uri) {
  console.warn('[MongoDB] MONGODB_URI is not set. Database operations will fail until configured.');
}

export async function getMongoConnection(): Promise<MongoConnection> {
  if (!uri) {
    throw new Error('MONGODB_URI environment variable is required for database access.');
  }

  if (global.__mongoConnection) {
    return global.__mongoConnection;
  }

  const client = new MongoClient(uri);
  await client.connect();

  const connection: MongoConnection = {
    client,
    db: client.db(dbName),
  };

  if (process.env.NODE_ENV !== 'production') {
    global.__mongoConnection = connection;
  }

  return connection;
}

export async function getMongoDb(): Promise<Db> {
  const { db } = await getMongoConnection();
  return db;
}
