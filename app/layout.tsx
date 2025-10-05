import type { Metadata } from 'next';
import './globals.css';
import { ClerkProvider } from '@clerk/nextjs';
import { AppHeader } from '@/components/layout/AppHeader';

export const metadata: Metadata = {
  title: 'Guardrails: Atomic',
  description: 'AI-powered code generation with formal correctness guarantees',
};

export default function RootLayout({
  children,
}: {
  children: React.ReactNode;
}) {
  return (
    <ClerkProvider>
      <html lang="en">
        <body className="bg-gray-50 min-h-screen">
          <AppHeader />
          <main className="container mx-auto p-4 sm:p-6 lg:p-8">
            {children}
          </main>
        </body>
      </html>
    </ClerkProvider>
  );
}
