"use client";

import Link from 'next/link';
import { ShieldCheck } from 'lucide-react';
import { SignedIn, SignedOut, UserButton } from '@clerk/nextjs';
import { Button } from '@/components/ui/button';
import { Menubar, MenubarMenu, MenubarTrigger } from '@/components/ui/menubar';

export function AppHeader() {
  return (
    <header className="bg-white border-b">
      <div className="container mx-auto flex items-center justify-between p-4">
        <Link href="/" className="flex items-center gap-2">
          <ShieldCheck className="h-6 w-6" />
          <span className="font-bold text-lg">Guardrails: Atomic</span>
        </Link>

        <div className="flex items-center gap-4">
          <Menubar>
            <MenubarMenu>
              <MenubarTrigger asChild>
                <Link href="/">Home</Link>
              </MenubarTrigger>
            </MenubarMenu>
            <MenubarMenu>
              <MenubarTrigger asChild>
                <Link href="/verify">Verify</Link>
              </MenubarTrigger>
            </MenubarMenu>
            <MenubarMenu>
              <MenubarTrigger asChild>
                <Link href="/examples">Examples</Link>
              </MenubarTrigger>
            </MenubarMenu>
            <SignedIn>
              <MenubarMenu>
                <MenubarTrigger asChild>
                  <Link href="/dashboard/history">History</Link>
                </MenubarTrigger>
              </MenubarMenu>
            </SignedIn>
          </Menubar>

          <SignedOut>
            <Button asChild size="sm">
              <Link href="/sign-in">Sign in</Link>
            </Button>
          </SignedOut>

          <SignedIn>
            <UserButton afterSignOutUrl="/" appearance={{ elements: { userButtonAvatarBox: 'h-8 w-8' } }} />
          </SignedIn>
        </div>
      </div>
    </header>
  );
}
