import Link from 'next/link';
import { Button } from '@/components/ui/button';
import { Card, CardHeader, CardTitle, CardDescription, CardContent } from '@/components/ui/card';

export default function Home() {
  return (
    <div className="flex flex-col items-center justify-center min-h-[80vh]">
      <Card className="w-full max-w-3xl shadow-lg hover:shadow-xl transition-shadow duration-300">
        <CardHeader className="text-center p-8 bg-gradient-to-br from-gray-100 to-gray-200 rounded-t-lg">
          <CardTitle className="text-4xl">Guardrails: Atomic</CardTitle>
          <CardDescription className="text-lg text-gray-600 mt-2">AI-powered code generation with formal correctness guarantees.</CardDescription>
        </CardHeader>
        <CardContent className="p-8">
          <p className="text-center text-gray-700 mb-6">Generate distributed system handlers proven correct by TLA+ model checking. Describe your desired behavior in plain English, and let Guardrails: Atomic generate a formally verified implementation.</p>
          <div className="flex gap-4 justify-center">
            <Link href="/verify">
              <Button size="lg">Start Verification</Button>
            </Link>
            <Link href="/examples">
              <Button size="lg" variant="outline">View Examples</Button>
            </Link>
          </div>
        </CardContent>
      </Card>
    </div>
  );
}
